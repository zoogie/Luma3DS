/*
*   This file is part of Luma3DS
*   Copyright (C) 2016 Aurora Wright, TuxSH
*
*   This program is free software: you can redistribute it and/or modify
*   it under the terms of the GNU General Public License as published by
*   the Free Software Foundation, either version 3 of the License, or
*   (at your option) any later version.
*
*   This program is distributed in the hope that it will be useful,
*   but WITHOUT ANY WARRANTY; without even the implied warranty of
*   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
*   GNU General Public License for more details.
*
*   You should have received a copy of the GNU General Public License
*   along with this program.  If not, see <http://www.gnu.org/licenses/>.
*
*   Additional Terms 7.b of GPLv3 applies to this file: Requiring preservation of specified
*   reasonable legal notices or author attributions in that material or in the Appropriate Legal
*   Notices displayed by works containing it.
*/

#include "firm.h"
#include "config.h"
#include "utils.h"
#include "fs.h"
#include "exceptions.h"
#include "patches.h"
#include "memory.h"
#include "strings.h"
#include "cache.h"
#include "emunand.h"
#include "crypto.h"
#include "screen.h"
#include "fmt.h"
#include "../build/bundled.h"

static Firm *firm = (Firm *)0x20001000;

static __attribute__((noinline)) bool overlaps(u32 as, u32 ae, u32 bs, u32 be)
{
    if(as <= bs && bs <= ae)
        return true;
    if(bs <= as && as <= be)
        return true;
    return false;
}

static __attribute__((noinline)) bool inRange(u32 as, u32 ae, u32 bs, u32 be)
{
   if(as >= bs && ae <= be)
        return true;
   return false;
}

static bool checkFirm(u32 firmSize)
{
    if(memcmp(firm->magic, "FIRM", 4) != 0 || firm->arm9Entry == NULL) //Allow for the ARM11 entrypoint to be zero in which case nothing is done on the ARM11 side
        return false;

    bool arm9EpFound = false,
         arm11EpFound = false;

    u32 size = 0x200;
    for(u32 i = 0; i < 4; i++)
        size += firm->section[i].size;

    if(firmSize < size) return false;

    for(u32 i = 0; i < 4; i++)
    {
        FirmSection *section = &firm->section[i];

        //Allow empty sections
        if(section->size == 0)
            continue;

        if((section->offset < 0x200) ||
           (section->address + section->size < section->address) || //Overflow check
           ((u32)section->address & 3) || (section->offset & 0x1FF) || (section->size & 0x1FF) || //Alignment check
           (overlaps((u32)section->address, (u32)section->address + section->size, (u32)firm, (u32)firm + size)) ||
           ((!inRange((u32)section->address, (u32)section->address + section->size, 0x08000000, 0x08000000 + 0x00100000)) &&
            (!inRange((u32)section->address, (u32)section->address + section->size, 0x18000000, 0x18000000 + 0x00600000)) &&
            (!inRange((u32)section->address, (u32)section->address + section->size, 0x1FF00000, 0x1FFFFC00)) &&
            (!inRange((u32)section->address, (u32)section->address + section->size, 0x20000000, 0x20000000 + 0x8000000))))
            return false;

        __attribute__((aligned(4))) u8 hash[0x20];

        sha(hash, (u8 *)firm + section->offset, section->size, SHA_256_MODE);

        if(memcmp(hash, section->hash, 0x20) != 0)
            return false;

        if(firm->arm9Entry >= section->address && firm->arm9Entry < (section->address + section->size))
            arm9EpFound = true;

        if(firm->arm11Entry >= section->address && firm->arm11Entry < (section->address + section->size))
            arm11EpFound = true;
    }

    return arm9EpFound && (firm->arm11Entry == NULL || arm11EpFound);
}

static inline u32 loadFirmFromStorage(FirmwareType firmType)
{
    const char *firmwareFiles[] = {
        "native.firm",
        "twl.firm",
        "agb.firm",
        "safe.firm",
        "sysupdater.firm"
    },
               *cetkFiles[] = {
        "cetk",
        "cetk_twl",
        "cetk_agb",
        "cetk_safe",
        "cetk_sysupdater"
    };

    u32 firmSize = fileRead(firm, firmType == NATIVE_FIRM1X2X ? firmwareFiles[0] : firmwareFiles[(u32)firmType], 0x400000 + sizeof(Cxi) + 0x200);

    if(!firmSize) return 0;

    static const char *extFirmError = "The external FIRM is not valid.";

    if(firmSize <= sizeof(Cxi) + 0x200) error(extFirmError);

    if(memcmp(firm, "FIRM", 4) != 0)
    {
        if(firmSize <= sizeof(Cxi) + 0x400) error(extFirmError);

        u8 cetk[0xA50];

        if(fileRead(cetk, firmType == NATIVE_FIRM1X2X ? cetkFiles[0] : cetkFiles[(u32)firmType], sizeof(cetk)) != sizeof(cetk))
            error("The cetk is missing or corrupted.");

        firmSize = decryptNusFirm((Ticket *)(cetk + 0x140), (Cxi *)firm, firmSize);

        if(!firmSize) error("Unable to decrypt the external FIRM.");
    }

    return firmSize;
}

u32 loadNintendoFirm(FirmwareType *firmType, FirmwareSource nandType, bool loadFromStorage, bool isSafeMode)
{
    //Load FIRM from CTRNAND
    u32 firmVersion = firmRead(firm, (u32)*firmType);

    if(firmVersion == 0xFFFFFFFF) error("Failed to get the CTRNAND FIRM.");

    bool mustLoadFromStorage = false;

    if(!ISN3DS && *firmType == NATIVE_FIRM && !ISDEVUNIT)
    {
        static const char *oldEmuNandError = "An old unsupported EmuNAND has been detected.\nLuma3DS is unable to boot it.";

        if(firmVersion < 0x18)
        {
            //We can't boot < 3.x EmuNANDs
            if(nandType != FIRMWARE_SYSNAND) error(oldEmuNandError);

            if(isSafeMode) error("SAFE_MODE is not supported on 1.x/2.x FIRM.");

            *firmType = NATIVE_FIRM1X2X;
        }
        else if(firmVersion < 0x25 && nandType != FIRMWARE_SYSNAND)
        {
            if(firmVersion < 0x1D) error(oldEmuNandError);

            mustLoadFromStorage = true;
        }
    }

    bool loadedFromStorage = false;
    u32 firmSize;

    if(loadFromStorage || mustLoadFromStorage)
    {
        u32 result = loadFirmFromStorage(*firmType);

        if(result != 0)
        {
            loadedFromStorage = true;
            firmSize = result;
        }
    }

    if(!loadedFromStorage)
    {
        if(mustLoadFromStorage) error("An old unsupported EmuNAND has been detected.\nCopy an external FIRM to boot.");
        firmSize = decryptExeFs((Cxi *)firm);
        if(!firmSize) error("Unable to decrypt the CTRNAND FIRM.");
    }

    if(!checkFirm(firmSize)) error("The %s FIRM is invalid or corrupted.", loadedFromStorage ? "external" : "CTRNAND");

    //Check that the FIRM is right for the console from the ARM9 section address
    if((firm->section[3].offset != 0 ? firm->section[3].address : firm->section[2].address) != (ISN3DS ? (u8 *)0x8006000 : (u8 *)0x8006800))
        error("The %s FIRM is not for this console.", loadedFromStorage ? "external" : "CTRNAND");

    return loadedFromStorage || ISDEVUNIT ? 0xFFFFFFFF : firmVersion;
}

void loadHomebrewFirm(u32 pressed)
{
    char path[10 + 255];
    bool found = !pressed ? payloadMenu(path) : findPayload(path, pressed);

    if(!found) return;

    u32 maxPayloadSize = (u32)((u8 *)0x27FFE000 - (u8 *)firm),
        payloadSize = fileRead(firm, path, maxPayloadSize);

    if(payloadSize <= 0x200 || !checkFirm(payloadSize)) error("The payload is invalid or corrupted.");

    char absPath[24 + 255];

    if(isSdMode) sprintf(absPath, "sdmc:/luma/%s", path);
    else sprintf(absPath, "nand:/rw/luma/%s", path);

    char *argv[2] = {absPath, (char *)fbs};

    initScreens();

    launchFirm((firm->reserved2[0] & 1) ? 2 : 1, argv);
}

static inline void mergeSection0(FirmwareType firmType, bool loadFromStorage)
{
    u32 maxModuleSize = firmType == NATIVE_FIRM ? 0x60000 : 0x600000,
        srcModuleSize,
        dstModuleSize;
    const char *extModuleSizeError = "The external FIRM modules are too large.";

    for(u8 *src = (u8 *)firm + firm->section[0].offset, *srcEnd = src + firm->section[0].size, *dst = firm->section[0].address;
        src < srcEnd; src += srcModuleSize, dst += dstModuleSize, maxModuleSize -= dstModuleSize)
    {
        srcModuleSize = ((Cxi *)src)->ncch.contentSize * 0x200;
        const char *moduleName = ((Cxi *)src)->exHeader.systemControlInfo.appTitle;

        if(loadFromStorage)
        {
            char fileName[24];

            //Read modules from files if they exist
            sprintf(fileName, "sysmodules/%.8s.cxi", moduleName);

            dstModuleSize = getFileSize(fileName);

            if(dstModuleSize != 0)
            {
                if(dstModuleSize > maxModuleSize) error(extModuleSizeError);

                if(dstModuleSize <= sizeof(Cxi) + 0x200 ||
                   fileRead(dst, fileName, dstModuleSize) != dstModuleSize ||
                   memcmp(((Cxi *)dst)->ncch.magic, "NCCH", 4) != 0 ||
                   memcmp(moduleName, ((Cxi *)dst)->exHeader.systemControlInfo.appTitle, sizeof(((Cxi *)dst)->exHeader.systemControlInfo.appTitle)) != 0)
                    error("An external FIRM module is invalid or corrupted.");

                continue;
            }
        }

        u8 *module;

        if(firmType == NATIVE_FIRM && memcmp(moduleName, "loader", 6) == 0)
        {
            module = (u8 *)0x1FF60000;
            dstModuleSize = LUMA_SECTION0_SIZE;
        }
        else
        {
            module = src;
            dstModuleSize = srcModuleSize;
        }

        if(dstModuleSize > maxModuleSize) error(extModuleSizeError);

        memcpy(dst, module, dstModuleSize);
    }
}

u32 patchNativeFirm(u32 firmVersion, FirmwareSource nandType, bool loadFromStorage, bool isSafeMode, bool doUnitinfoPatch, bool enableExceptionHandlers)
{
    u8 *arm9Section = (u8 *)firm + firm->section[2].offset,
       *arm11Section1 = (u8 *)firm + firm->section[1].offset;

    if(ISN3DS)
    {
        //Decrypt ARM9Bin and patch ARM9 entrypoint to skip kernel9loader
        kernel9Loader((Arm9Bin *)arm9Section);
        firm->arm9Entry = (u8 *)0x801B01C;
    }
    
    //Find the Process9 .code location, size and memory address
    u32 process9Size,
        process9MemAddr;
    u8 *process9Offset = getProcess9Info(arm9Section, firm->section[2].size, &process9Size, &process9MemAddr);

    //Find the Kernel11 SVC table and handler, exceptions page and free space locations
    u32 baseK11VA;
    u8 *freeK11Space;
    u32 *arm11SvcHandler,
        *arm11DAbtHandler,
        *arm11ExceptionsPage,
        *arm11SvcTable = getKernel11Info(arm11Section1, firm->section[1].size, &baseK11VA, &freeK11Space, &arm11SvcHandler, &arm11DAbtHandler, &arm11ExceptionsPage);

    u32 kernel9Size = (u32)(process9Offset - arm9Section) - sizeof(Cxi) - 0x200,
        ret = 0;

    //Apply signature patches
    ret += patchSignatureChecks(process9Offset, process9Size);

    //Apply EmuNAND patches
    if(nandType != FIRMWARE_SYSNAND) ret += patchEmuNand(arm9Section, kernel9Size, process9Offset, process9Size, firm->section[2].address);

    //Apply FIRM0/1 writes patches on SysNAND to protect A9LH
    else ret += patchFirmWrites(process9Offset, process9Size);

    //Apply firmlaunch patches
    ret += patchFirmlaunches(process9Offset, process9Size, process9MemAddr);

    //Apply dev unit check patches related to NCCH encryption
    if(!ISDEVUNIT)
    {
        ret += patchZeroKeyNcchEncryptionCheck(process9Offset, process9Size);
        ret += patchNandNcchEncryptionCheck(process9Offset, process9Size);
    }

    //11.0 FIRM patches
    if(firmVersion >= (ISN3DS ? 0x21 : 0x52))
    {
        //Apply anti-anti-DG patches
        ret += patchTitleInstallMinVersionChecks(process9Offset, process9Size, firmVersion);

        //Restore svcBackdoor
        ret += reimplementSvcBackdoor(arm11Section1, arm11SvcTable, baseK11VA, &freeK11Space);
    }

    //Stub svc 0x59 on 11.3+ FIRMs
    if(firmVersion >= (ISN3DS ? 0x2D : 0x5C)) ret += stubSvcRestrictGpuDma(arm11Section1, arm11SvcTable, baseK11VA);

    ret += implementSvcGetCFWInfo(arm11Section1, arm11SvcTable, baseK11VA, &freeK11Space, isSafeMode);

    //Apply UNITINFO patches
    if(doUnitinfoPatch)
    {
        ret += patchUnitInfoValueSet(arm9Section, kernel9Size);
        if(!ISDEVUNIT) ret += patchCheckForDevCommonKey(process9Offset, process9Size);
    }

    if(enableExceptionHandlers)
    {
        if(firmVersion >= 0x1D)
        {
            //ARM11 exception handlers
            u32 codeSetOffset,
                stackAddress = getInfoForArm11ExceptionHandlers(arm11Section1, firm->section[1].size, &codeSetOffset, firmVersion);

            if(stackAddress != 0)
            {
                ret += installArm11Handlers(arm11ExceptionsPage, stackAddress, codeSetOffset, arm11DAbtHandler, baseK11VA + ((u8 *)arm11DAbtHandler - arm11Section1));
                patchSvcBreak11(arm11Section1, arm11SvcTable, baseK11VA);
                ret += patchKernel11Panic(arm11Section1, firm->section[1].size);
            }
        }

        //ARM9 exception handlers
        ret += patchArm9ExceptionHandlersInstall(arm9Section, kernel9Size);
        ret += patchSvcBreak9(arm9Section, kernel9Size, (u32)firm->section[2].address);
        ret += patchKernel9Panic(arm9Section, kernel9Size);
    }

    bool patchAccess = CONFIG(PATCHACCESS),
         patchGames = CONFIG(PATCHGAMES);

    if(patchAccess || patchGames)
    {
        ret += patchK11ModuleChecks(arm11Section1, firm->section[1].size, &freeK11Space, patchGames);

        if(patchAccess)
        {
            ret += patchArm11SvcAccessChecks(arm11SvcHandler, (u32 *)(arm11Section1 + firm->section[1].size));
            ret += patchP9AccessChecks(process9Offset, process9Size);
        }
    }

    mergeSection0(NATIVE_FIRM, loadFromStorage);
    firm->section[0].size = 0;

    return ret;
}

u32 patchTwlFirm(u32 firmVersion, bool loadFromStorage, bool doUnitinfoPatch)
{
    u8 *arm9Section = (u8 *)firm + firm->section[3].offset;

    //On N3DS, decrypt ARM9Bin and patch ARM9 entrypoint to skip kernel9loader
    if(ISN3DS)
    {
        kernel9Loader((Arm9Bin *)arm9Section);
        firm->arm9Entry = (u8 *)0x801301C;
    }

    //Find the Process9 .code location, size and memory address
    u32 process9Size,
        process9MemAddr;
    u8 *process9Offset = getProcess9Info(arm9Section, firm->section[3].size, &process9Size, &process9MemAddr);

    u32 kernel9Size = (u32)(process9Offset - arm9Section) - sizeof(Cxi) - 0x200,
        ret = 0;

    ret += patchLgySignatureChecks(process9Offset, process9Size);
    ret += patchTwlInvalidSignatureChecks(process9Offset, process9Size);
    ret += patchTwlNintendoLogoChecks(process9Offset, process9Size);
    ret += patchTwlWhitelistChecks(process9Offset, process9Size);
    if(ISN3DS || firmVersion > 0x11) ret += patchTwlFlashcartChecks(process9Offset, process9Size, firmVersion);
    else if(!ISN3DS && firmVersion == 0x11) ret += patchOldTwlFlashcartChecks(process9Offset, process9Size);
    ret += patchTwlShaHashChecks(process9Offset, process9Size);

    //Apply UNITINFO patch
    if(doUnitinfoPatch) ret += patchUnitInfoValueSet(arm9Section, kernel9Size);

    if(loadFromStorage)
    {
        mergeSection0(TWL_FIRM, true);
        firm->section[0].size = 0;
    }

    return ret;
}

u32 patchAgbFirm(bool loadFromStorage, bool doUnitinfoPatch)
{
    u8 *arm9Section = (u8 *)firm + firm->section[3].offset;

    //On N3DS, decrypt ARM9Bin and patch ARM9 entrypoint to skip kernel9loader
    if(ISN3DS)
    {
        kernel9Loader((Arm9Bin *)arm9Section);
        firm->arm9Entry = (u8 *)0x801301C;
    }

    //Find the Process9 .code location, size and memory address
    u32 process9Size,
        process9MemAddr;
    u8 *process9Offset = getProcess9Info(arm9Section, firm->section[3].size, &process9Size, &process9MemAddr);

    u32 kernel9Size = (u32)(process9Offset - arm9Section) - sizeof(Cxi) - 0x200,
        ret = 0;

    ret += patchLgySignatureChecks(process9Offset, process9Size);
    if(CONFIG(SHOWGBABOOT)) ret += patchAgbBootSplash(process9Offset, process9Size);

    //Apply UNITINFO patch
    if(doUnitinfoPatch) ret += patchUnitInfoValueSet(arm9Section, kernel9Size);

    if(loadFromStorage)
    {
        mergeSection0(AGB_FIRM, true);
        firm->section[0].size = 0;
    }

    return ret;
}

u32 patch1x2xNativeAndSafeFirm(bool enableExceptionHandlers)
{
    u8 *arm9Section = (u8 *)firm + firm->section[2].offset;

    if(ISN3DS)
    {
        //Decrypt ARM9Bin and patch ARM9 entrypoint to skip kernel9loader
        kernel9Loader((Arm9Bin *)arm9Section);
        firm->arm9Entry = (u8 *)0x801B01C;
    }

    //Find the Process9 .code location, size and memory address
    u32 process9Size,
        process9MemAddr;
    u8 *process9Offset = getProcess9Info(arm9Section, firm->section[2].size, &process9Size, &process9MemAddr);

    u32 kernel9Size = (u32)(process9Offset - arm9Section) - sizeof(Cxi) - 0x200,
        ret = 0;

    ret += ISN3DS ? patchFirmWrites(process9Offset, process9Size) : patchOldFirmWrites(process9Offset, process9Size);

    ret += ISN3DS ? patchSignatureChecks(process9Offset, process9Size) : patchOldSignatureChecks(process9Offset, process9Size);

    if(enableExceptionHandlers)
    {
        //ARM9 exception handlers
        ret += patchArm9ExceptionHandlersInstall(arm9Section, kernel9Size);
        ret += patchSvcBreak9(arm9Section, kernel9Size, (u32)firm->section[2].address);
    }

    return ret;
}

void launchFirm(int argc, char **argv)
{
    u32 *chainloaderAddress = (u32 *)0x01FF9000;

    prepareArm11ForFirmlaunch();

    memcpy(chainloaderAddress, chainloader_bin, chainloader_bin_size);

    // No need to flush caches here, the chainloader is in ITCM
    ((void (*)(int, char **, Firm *))chainloaderAddress)(argc, argv, firm);
}
