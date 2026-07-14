#include <windows.h>
#include <dbghelp.h>
#include <stdint.h>
#include <string.h>

#pragma comment(linker, "/EXPORT:MiniDumpWriteDump=_MiniDumpWriteDump@28")

typedef BOOL (WINAPI *MiniDumpWriteDumpFunc)(
    HANDLE,
    DWORD,
    HANDLE,
    MINIDUMP_TYPE,
    PMINIDUMP_EXCEPTION_INFORMATION,
    PMINIDUMP_USER_STREAM_INFORMATION,
    PMINIDUMP_CALLBACK_INFORMATION);

typedef void* (__thiscall *PqChangeStageDeserializeFunc)(void* thisObj, void* packet);
typedef void* (__thiscall *PacketDeserializeFunc)(void* thisObj, void* packet);
typedef void* (__cdecl *ReadPacketWStringFunc)(void* stream, void* outString);
typedef void (__thiscall *StringOpFunc)(void* thisObj);
typedef void (__thiscall *PacketSerializeFunc)(void* thisObj, void* packet);
typedef void (__thiscall *PacketSerializeBaseFunc)(void* thisObj, void* packet);
typedef void* (__cdecl *PacketWriteVec3Func)(void* packet, const void* vec3);
typedef void* (__cdecl *PacketWriteVecArray1CFunc)(void* packet, const void* vecRange);
typedef void* (__cdecl *OpenPacketStringNodeFunc)(void* packet, void* wideString);
typedef void (__thiscall *StreamWriteScalarFunc)(void* streamObj, unsigned int value);
typedef void (__thiscall *StreamWriteBlobFunc)(void* streamObj, const void* data, unsigned int size);

static MiniDumpWriteDumpFunc realMiniDumpWriteDump = NULL;

static volatile LONG stageCompatApplied = 0;
static volatile LONG moveInventoryReadApplied = 0;
static volatile LONG moveInventorySlotTypeCompatApplied = 0;
static volatile LONG moveInventoryDirectApplyApplied = 0;
static volatile LONG openExteriorCellMaskCompatApplied = 0;
static volatile LONG npcCompatApplied = 0;
static const uintptr_t stageVTableOffset     = 0x004DB8B4; 
static const uintptr_t moveInventoryVTableOffset = 0x004D9E1C; 
static const uintptr_t openExteriorCellMaskOffset = 0x00080500; 
static const uintptr_t moveSlotTypeTableOffset       = 0x004DE240; 
static const uintptr_t readPacketWStringOffset     = 0x00002540; 
static const uintptr_t stringInitOffset            = 0x0001BEC0; 
static const uintptr_t stringFreeOffset            = 0x0001DA20; 

static const uintptr_t pcAddNpcVTableOffset          = 0x004D6AB4; 
static const uintptr_t pcUpdateNpcVTableOffset       = 0x004D6AD8; 
static const uintptr_t packetSerializeBaseOffset   = 0x00333ED0; 
static const uintptr_t packetWriteVec3Offset       = 0x00016900; 
static const uintptr_t packetWriteVecArray1COffset = 0x00015DE0; 
static const uintptr_t openPacketStringNodeOffset  = 0x000028E0; 

static const uintptr_t directApplyOffsets[] = {
    0x0015F70E, 
    0x0015F937, 
    0x0015FBAF, 
    0x0015FDDD, 
    0x001600BD, 
    0x001608EE, 
};

static const int npcMaxPerPacket = 0x20;
static const size_t npcAddEntrySizeServer = 0x50;
static const size_t npcUpdateEntrySizeServer = 0x18;
static const size_t clientNpcEntrySize = 0x58;
static const int npcCacheCapacity = 256;

static volatile LONG npcCacheState = 0;
static CRITICAL_SECTION npcCacheCs;
static BYTE npcCacheData[npcCacheCapacity][clientNpcEntrySize];
static ULONGLONG npcCacheKeys[npcCacheCapacity];
static BYTE npcCacheUsed[npcCacheCapacity];
static volatile LONG npcCacheWriteCursor = 0;

static PqChangeStageDeserializeFunc originalStageRead = NULL;
static PacketDeserializeFunc originalMoveInventoryItemRead = NULL;
static ReadPacketWStringFunc readPacketWString = NULL;
static StringOpFunc stringInit = NULL;
static StringOpFunc stringFree = NULL;

static PacketSerializeFunc originalPcAddNpcWrite = NULL;
static PacketSerializeFunc originalPcUpdateNpcWrite = NULL;
static PacketSerializeBaseFunc packetSerializeBase = NULL;
static PacketWriteVec3Func packetWriteVec3 = NULL;
static PacketWriteVecArray1CFunc packetWriteVecArray1C = NULL;
static OpenPacketStringNodeFunc openPacketStringNode = NULL;



static BOOL IsValidPointer(const void* p) {
    MEMORY_BASIC_INFORMATION mbi;
    if (VirtualQuery(p, &mbi, sizeof(mbi)) == 0) {
        return FALSE;
    }
    if (mbi.State != MEM_COMMIT) {
        return FALSE;
    }
    if ((mbi.Protect & PAGE_NOACCESS) != 0) {
        return FALSE;
    }
    if ((mbi.Protect & PAGE_GUARD) != 0) {
        return FALSE;
    }
    return TRUE;
}


static BOOL PatchByte(uintptr_t addr, BYTE value) {
    BYTE* p = (BYTE*)addr;
    if (!IsValidPointer(p)) {
        return FALSE;
    }

    __try {
        if (p[-3] != 0xC6 || p[-1] != 0x24) {
            return FALSE;
        }
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        return FALSE;
    }

    DWORD oldProtect = 0;
    if (!VirtualProtect(p, sizeof(BYTE), PAGE_EXECUTE_READWRITE, &oldProtect)) {
        return FALSE;
    }
    *p = value;
    FlushInstructionCache(GetCurrentProcess(), p, sizeof(BYTE));
    DWORD dummy = 0;
    VirtualProtect(p, sizeof(BYTE), oldProtect, &dummy);
    return TRUE;
}

static BOOL ApplyMoveInventoryDirectApply(uintptr_t base) {
    if (InterlockedCompareExchange(&moveInventoryDirectApplyApplied, 0, 0) != 0) {
        return TRUE;
    }

    for (size_t i = 0; i < sizeof(directApplyOffsets) / sizeof(directApplyOffsets[0]); ++i) {
        uintptr_t immAddr = base + directApplyOffsets[i];
        if (!PatchByte(immAddr, 1u)) {
            return FALSE;
        }
    }

    InterlockedExchange(&moveInventoryDirectApplyApplied, 1);
    return TRUE;
}

static unsigned int RemapMoveInventorySlot(unsigned int slot) {
    return slot & 0xFFu;
}

static int ClampNpcCount(int rawCount, BOOL* changed) {
    int safeCount = rawCount;
    if (safeCount < 0) {
        safeCount = 0;
    } else if (safeCount > npcMaxPerPacket) {
        safeCount = npcMaxPerPacket;
    }

    if (changed) {
        *changed = (safeCount != rawCount) ? TRUE : FALSE;
    }
    return safeCount;
}

static BOOL InitNpcCache(void) {
    LONG state = InterlockedCompareExchange(&npcCacheState, 0, 0);
    if (state == 2) {
        return TRUE;
    }

    if (state == 0 && InterlockedCompareExchange(&npcCacheState, 1, 0) == 0) {
        InitializeCriticalSection(&npcCacheCs);
        ZeroMemory(npcCacheData, sizeof(npcCacheData));
        ZeroMemory(npcCacheKeys, sizeof(npcCacheKeys));
        ZeroMemory(npcCacheUsed, sizeof(npcCacheUsed));
        InterlockedExchange(&npcCacheWriteCursor, 0);
        InterlockedExchange(&npcCacheState, 2);
        return TRUE;
    }

    for (int i = 0; i < 100; ++i) {
        if (InterlockedCompareExchange(&npcCacheState, 0, 0) == 2) {
            return TRUE;
        }
        Sleep(0);
    }
    return FALSE;
}

static ULONGLONG ReadU64(const BYTE* p) {
    ULONGLONG v = 0;
    if (!p) {
        return 0;
    }
    memcpy(&v, p, sizeof(v));
    return v;
}

static int FindNpcCacheIndex(ULONGLONG key) {
    for (int i = 0; i < npcCacheCapacity; ++i) {
        if (npcCacheUsed[i] && npcCacheKeys[i] == key) {
            return i;
        }
    }
    return -1;
}

static BOOL GetNpcFromCache(ULONGLONG key, BYTE* clientEntryOut) {
    if (!clientEntryOut || key == 0 || !InitNpcCache()) {
        return FALSE;
    }

    EnterCriticalSection(&npcCacheCs);
    int slot = FindNpcCacheIndex(key);
    if (slot >= 0) {
        memcpy(clientEntryOut, npcCacheData[slot], clientNpcEntrySize);
        LeaveCriticalSection(&npcCacheCs);
        return TRUE;
    }
    LeaveCriticalSection(&npcCacheCs);
    return FALSE;
}

static void SaveNpcToCache(const BYTE* clientEntry) {
    if (!clientEntry || !InitNpcCache()) {
        return;
    }

    ULONGLONG key = ReadU64(clientEntry + 0x00);
    if (key == 0) {
        return;
    }

    EnterCriticalSection(&npcCacheCs);

    int slot = FindNpcCacheIndex(key);
    if (slot < 0) {
        for (int i = 0; i < npcCacheCapacity; ++i) {
            if (!npcCacheUsed[i]) {
                slot = i;
                break;
            }
        }
    }
    if (slot < 0) {
        LONG cursor = InterlockedIncrement(&npcCacheWriteCursor);
        if (cursor < 0) {
            cursor = -cursor;
        }
        slot = (int)(cursor % npcCacheCapacity);
    }

    npcCacheUsed[slot] = 1;
    npcCacheKeys[slot] = key;
    memcpy(npcCacheData[slot], clientEntry, clientNpcEntrySize);

    LeaveCriticalSection(&npcCacheCs);
}

static void CacheNpcAddData(const BYTE* serverEntry, BYTE* clientEntry) {
    if (!serverEntry || !clientEntry) {
        return;
    }

    ZeroMemory(clientEntry, clientNpcEntrySize);

    memcpy(clientEntry + 0x00, serverEntry + 0x00, 8);
    memcpy(clientEntry + 0x08, serverEntry + 0x08, 4);
    memcpy(clientEntry + 0x0C, serverEntry + 0x0C, 2);
    memcpy(clientEntry + 0x10, serverEntry + 0x10, 12);
    memcpy(clientEntry + 0x1C, serverEntry + 0x1C, 12);
    memcpy(clientEntry + 0x2C, serverEntry + 0x2C, 4);
    clientEntry[0x30] = serverEntry[0x30];
    memcpy(clientEntry + 0x32, serverEntry + 0x32, 2);
    memset(clientEntry + 0x34, 0, 8);
    memset(clientEntry + 0x3C, 0, 8);
    clientEntry[0x48] = serverEntry[0x40];
    memcpy(clientEntry + 0x4C, serverEntry + 0x44, 4);
    memcpy(clientEntry + 0x50, serverEntry + 0x48, 8);
}

static void CacheNpcUpdateData(const BYTE* serverEntry, BYTE* clientEntry) {
    if (!serverEntry || !clientEntry) {
        return;
    }

    ULONGLONG key = ReadU64(serverEntry + 0x00);
    BOOL found = GetNpcFromCache(key, clientEntry);
    if (!found) {
        ZeroMemory(clientEntry, clientNpcEntrySize);
        memcpy(clientEntry + 0x00, serverEntry + 0x00, 8);
    }

    
    clientEntry[0x48] = serverEntry[0x08];
    memcpy(clientEntry + 0x4C, serverEntry + 0x0C, 4);
    memcpy(clientEntry + 0x50, serverEntry + 0x10, 8);
}

static void* __fastcall HookedPqChangeStageRead(void* thisObj, void* edx, void* packet) {
    (void)edx;

    if (!originalStageRead) {
        return packet;
    }

    void* stream = originalStageRead(thisObj, packet);
    if (!stream || !readPacketWString || !stringInit || !stringFree) {
        return stream;
    }

    DWORD tmpWideString = 0;
    stringInit(&tmpWideString);
    __try {
        stream = readPacketWString(stream, &tmpWideString);
    } __except (EXCEPTION_EXECUTE_HANDLER) {
    }
    stringFree(&tmpWideString);
    return stream;
}

static BOOL ApplyMoveInventorySlotTypeCompat(uintptr_t base) {
    if (InterlockedCompareExchange(&moveInventorySlotTypeCompatApplied, 0, 0) != 0) {
        return TRUE;
    }

    unsigned short* slotTypeTable = (unsigned short*)(base + moveSlotTypeTableOffset);
    if (!IsValidPointer(slotTypeTable)) {
        return FALSE;
    }

    struct SlotPatch {
        unsigned int slot;
        unsigned short type;
    };

    static const SlotPatch alwaysPatches[] = {
        {42u, 126u},
        {43u, 127u},
        {44u, 102u},
        {46u, 129u},
        {47u, 130u},
    };

    DWORD oldProtect = 0;
    if (!VirtualProtect(slotTypeTable, 64u * sizeof(unsigned short), PAGE_EXECUTE_READWRITE, &oldProtect)) {
        return FALSE;
    }

    for (size_t i = 0; i < sizeof(alwaysPatches) / sizeof(alwaysPatches[0]); ++i) {
        slotTypeTable[alwaysPatches[i].slot] = alwaysPatches[i].type;
    }

    FlushInstructionCache(GetCurrentProcess(), slotTypeTable, 64u * sizeof(unsigned short));
    DWORD dummy = 0;
    VirtualProtect(slotTypeTable, 64u * sizeof(unsigned short), oldProtect, &dummy);

    InterlockedExchange(&moveInventorySlotTypeCompatApplied, 1);
    return TRUE;
}

static void* __fastcall HookedPqMoveInventoryItemRead(void* thisObj, void* edx, void* packet) {
    (void)edx;

    void* stream = packet;
    if (originalMoveInventoryItemRead) {
        stream = originalMoveInventoryItemRead(thisObj, packet);
    }
    if (!thisObj) {
        return stream;
    }

    __try {
        BYTE* p = (BYTE*)thisObj;
        unsigned int bRaw = (unsigned int)p[0x24];
        unsigned int eRaw = (unsigned int)p[0x3C];
        unsigned int gRaw = (unsigned int)p[0x44];
        unsigned int b = RemapMoveInventorySlot(bRaw);
        unsigned int e = RemapMoveInventorySlot(eRaw);
        unsigned int g = RemapMoveInventorySlot(gRaw);

        if (b != bRaw || e != eRaw || g != gRaw) {
            p[0x24] = (BYTE)b;
            p[0x3C] = (BYTE)e;
            p[0x44] = (BYTE)g;
        }
    } __except (EXCEPTION_EXECUTE_HANDLER) {
    }

    return stream;
}

static void* GetStreamObject(void* packetObj) {
    if (!packetObj) {
        return NULL;
    }
    __try {
        return *(void**)((BYTE*)packetObj + 0x10);
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        return NULL;
    }
}

static void* GetVTableFunc(void* streamObj, size_t byteOffset) {
    if (!streamObj) {
        return NULL;
    }
    __try {
        void** vtbl = *(void***)streamObj;
        if (!vtbl) {
            return NULL;
        }
        return vtbl[byteOffset / sizeof(void*)];
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        return NULL;
    }
}

static BOOL WriteScalarToStream(void* packetObj, size_t byteOffset, unsigned int value) {
    void* streamObj = GetStreamObject(packetObj);
    if (!streamObj) {
        return FALSE;
    }

    StreamWriteScalarFunc fn = (StreamWriteScalarFunc)GetVTableFunc(streamObj, byteOffset);
    if (!fn) {
        return FALSE;
    }
    fn(streamObj, value);
    return TRUE;
}

static BOOL WriteBlobToStream(void* packetObj, size_t byteOffset, const void* data, unsigned int size) {
    if (!data || size == 0) {
        return FALSE;
    }

    void* streamObj = GetStreamObject(packetObj);
    if (!streamObj) {
        return FALSE;
    }

    StreamWriteBlobFunc fn = (StreamWriteBlobFunc)GetVTableFunc(streamObj, byteOffset);
    if (!fn) {
        return FALSE;
    }
    fn(streamObj, data, size);
    return TRUE;
}

static BOOL WriteU8(void* packetObj, unsigned int value) {
    return WriteScalarToStream(packetObj, 0x1C, value & 0xFFu);
}

static BOOL WriteU16(void* packetObj, unsigned int value) {
    return WriteScalarToStream(packetObj, 0x20, value & 0xFFFFu);
}

static BOOL WriteU32(void* packetObj, unsigned int value) {
    return WriteScalarToStream(packetObj, 0x24, value);
}

static BOOL WriteBytes(void* packetObj, const void* data, unsigned int size) {
    return WriteBlobToStream(packetObj, 0x28, data, size);
}

static BOOL WriteNpcMetadata(void* packetObj, const BYTE* meta6) {
    if (!packetObj || !meta6) {
        return FALSE;
    }

    if (!WriteU8(packetObj, (unsigned int)meta6[0])) {
        return FALSE;
    }
    if (!WriteU8(packetObj, (unsigned int)meta6[1])) {
        return FALSE;
    }
    if (!WriteU16(packetObj, *(const unsigned short*)(meta6 + 2))) {
        return FALSE;
    }
    if (!WriteU16(packetObj, *(const unsigned short*)(meta6 + 4))) {
        return FALSE;
    }
    return TRUE;
}

static BOOL WriteNpcEntry(void* packet, const BYTE* clientEntry) {
    if (!packet || !clientEntry) {
        return FALSE;
    }

    if (!WriteBytes(packet, clientEntry + 0x00, 8)) {
        return FALSE;
    }
    if (!WriteU32(packet, *(const unsigned int*)(clientEntry + 0x08))) {
        return FALSE;
    }
    if (!WriteU16(packet, *(const unsigned short*)(clientEntry + 0x0C))) {
        return FALSE;
    }
    if (!packetWriteVec3(packet, (const void*)(clientEntry + 0x10))) {
        return FALSE;
    }
    if (!packetWriteVec3(packet, (const void*)(clientEntry + 0x1C))) {
        return FALSE;
    }

    void* nameNode = openPacketStringNode(packet, (void*)(clientEntry + 0x28));
    if (!nameNode) {
        return FALSE;
    }
    if (!WriteU32(nameNode, *(const unsigned int*)(clientEntry + 0x2C))) {
        return FALSE;
    }
    if (!WriteU8(nameNode, (unsigned int)clientEntry[0x30])) {
        return FALSE;
    }

    if (!WriteU16(packet, *(const unsigned short*)(clientEntry + 0x32))) {
        return FALSE;
    }
    
    if (!WriteNpcMetadata(packet, clientEntry + 0x34)) {
        return FALSE;
    }
    if (!packetWriteVecArray1C(packet, (const void*)(clientEntry + 0x3C))) {
        return FALSE;
    }
    if (!WriteU8(packet, (unsigned int)clientEntry[0x48])) {
        return FALSE;
    }
    if (!WriteU32(packet, *(const unsigned int*)(clientEntry + 0x4C))) {
        return FALSE;
    }
    if (!WriteBytes(packet, clientEntry + 0x50, 8)) {
        return FALSE;
    }
    return TRUE;
}

static BOOL WriteNpcAddEntry(void* packet, const BYTE* serverEntry) {
    if (!packet || !serverEntry) {
        return FALSE;
    }
    if (!WriteBytes(packet, serverEntry + 0x00, 8)) {
        return FALSE;
    }
    if (!WriteU32(packet, *(const unsigned int*)(serverEntry + 0x08))) {
        return FALSE;
    }
    if (!WriteU16(packet, *(const unsigned short*)(serverEntry + 0x0C))) {
        return FALSE;
    }
    if (!packetWriteVec3(packet, (const void*)(serverEntry + 0x10))) {
        return FALSE;
    }
    if (!packetWriteVec3(packet, (const void*)(serverEntry + 0x1C))) {
        return FALSE;
    }

    void* nameNode = openPacketStringNode(packet, (void*)(serverEntry + 0x28));
    if (!nameNode) {
        return FALSE;
    }
    if (!WriteU32(nameNode, *(const unsigned int*)(serverEntry + 0x2C))) {
        return FALSE;
    }
    if (!WriteU8(nameNode, (unsigned int)serverEntry[0x30])) {
        return FALSE;
    }

    if (!WriteU16(packet, *(const unsigned short*)(serverEntry + 0x32))) {
        return FALSE;
    }

    static const BYTE kNpcField34Default[6] = {0, 0, 0, 0, 0, 0};
    if (!WriteNpcMetadata(packet, kNpcField34Default)) {
        return FALSE;
    }

    // Old server +0x34 vector(0x1C) maps to client +0x3C
    if (!packetWriteVecArray1C(packet, (const void*)(serverEntry + 0x34))) {
        return FALSE;
    }

    if (!WriteU8(packet, (unsigned int)serverEntry[0x40])) {
        return FALSE;
    }
    if (!WriteU32(packet, *(const unsigned int*)(serverEntry + 0x44))) {
        return FALSE;
    }
    if (!WriteBytes(packet, serverEntry + 0x48, 8)) {
        return FALSE;
    }
    return TRUE;
}

static BOOL WritePcAddNpc(void* thisObj, void* packet) {
    if (!thisObj || !packet || !packetSerializeBase ||
        !packetWriteVec3 || !packetWriteVecArray1C || !openPacketStringNode) {
        return FALSE;
    }

    int rawCount = 0;
    __try {
        rawCount = *(int*)((BYTE*)thisObj + 0x14);
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        return FALSE;
    }
    int count = ClampNpcCount(rawCount, NULL);

    packetSerializeBase(thisObj, packet);
    if (!WriteU32(packet, (unsigned int)count)) {
        return FALSE;
    }

    for (int i = 0; i < count; ++i) {
        const BYTE* serverEntry = (const BYTE*)thisObj + 0x18 + ((size_t)i * npcAddEntrySizeServer);

        if (!WriteNpcAddEntry(packet, serverEntry)) {
            return FALSE;
        }

        BYTE clientEntry[clientNpcEntrySize];
        CacheNpcAddData(serverEntry, clientEntry);
        SaveNpcToCache(clientEntry);
    }
    return TRUE;
}

static BOOL WritePcUpdateNpc(void* thisObj, void* packet) {
    if (!thisObj || !packet || !packetSerializeBase ||
        !packetWriteVec3 || !packetWriteVecArray1C || !openPacketStringNode) {
        return FALSE;
    }

    int rawCount = 0;
    __try {
        rawCount = *(int*)((BYTE*)thisObj + 0x14);
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        return FALSE;
    }
    int count = ClampNpcCount(rawCount, NULL);

    packetSerializeBase(thisObj, packet);
    if (!WriteU32(packet, (unsigned int)count)) {
        return FALSE;
    }

    for (int i = 0; i < count; ++i) {
        const BYTE* serverEntry = (const BYTE*)thisObj + 0x18 + ((size_t)i * npcUpdateEntrySizeServer);

        BYTE clientEntry[clientNpcEntrySize];
        CacheNpcUpdateData(serverEntry, clientEntry);

        if (!WriteNpcEntry(packet, clientEntry)) {
            return FALSE;
        }
        SaveNpcToCache(clientEntry);
    }
    return TRUE;
}

static void __fastcall HookedPcAddNpcWrite(void* thisObj, void* edx, void* packet) {
    (void)edx;

    if (!originalPcAddNpcWrite) {
        return;
    }
    if (!thisObj || !packet) {
        originalPcAddNpcWrite(thisObj, packet);
        return;
    }

    int* countPtr = (int*)((BYTE*)thisObj + 0x14);
    int rawCount = 0;
    int safeCount = 0;
    BOOL changed = FALSE;

    __try {
        rawCount = *countPtr;
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        rawCount = 0;
    }
    safeCount = ClampNpcCount(rawCount, &changed);

    if (changed) {
        __try {
            *countPtr = safeCount;
        } __except (EXCEPTION_EXECUTE_HANDLER) {
            changed = FALSE;
        }
    }

    BOOL ok = WritePcAddNpc(thisObj, packet);
    if (!ok) {
        originalPcAddNpcWrite(thisObj, packet);
    }

    if (changed) {
        __try {
            *countPtr = rawCount;
        } __except (EXCEPTION_EXECUTE_HANDLER) {
        }
    }
}

static void __fastcall HookedPcUpdateNpcWrite(void* thisObj, void* edx, void* packet) {
    (void)edx;
    if (!originalPcUpdateNpcWrite) {
        return;
    }
    if (!thisObj || !packet) {
        originalPcUpdateNpcWrite(thisObj, packet);
        return;
    }

    int* countPtr = (int*)((BYTE*)thisObj + 0x14);
    int rawCount = 0;
    int safeCount = 0;
    BOOL changed = FALSE;

    __try {
        rawCount = *countPtr;
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        rawCount = 0;
    }
    safeCount = ClampNpcCount(rawCount, &changed);

    if (changed) {
        __try {
            *countPtr = safeCount;
        } __except (EXCEPTION_EXECUTE_HANDLER) {
            changed = FALSE;
        }
    }

    BOOL ok = WritePcUpdateNpc(thisObj, packet);
    if (!ok) {
        originalPcUpdateNpcWrite(thisObj, packet);
    }

    if (changed) {
        __try {
            *countPtr = rawCount;
        } __except (EXCEPTION_EXECUTE_HANDLER) {
        }
    }
}

static BOOL ApplyPqChangeStageCompat(uintptr_t base) {
    if (InterlockedCompareExchange(&stageCompatApplied, 0, 0) != 0) {
        return TRUE;
    }

    DWORD* vtable = (DWORD*)(base + stageVTableOffset);
    if (!IsValidPointer(vtable)) {
        return FALSE;
    }

    DWORD oldEntry1 = 0;
    __try {
        oldEntry1 = vtable[1];
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        return FALSE;
    }

    if (oldEntry1 < (DWORD)base || oldEntry1 > (DWORD)(base + 0x08000000)) {
        return FALSE;
    }

    originalStageRead = (PqChangeStageDeserializeFunc)(uintptr_t)oldEntry1;
    readPacketWString = (ReadPacketWStringFunc)(base + readPacketWStringOffset);
    stringInit = (StringOpFunc)(base + stringInitOffset);
    stringFree = (StringOpFunc)(base + stringFreeOffset);

    DWORD hook = (DWORD)(uintptr_t)&HookedPqChangeStageRead;
    DWORD oldProtect = 0;
    if (!VirtualProtect(&vtable[1], sizeof(hook), PAGE_EXECUTE_READWRITE, &oldProtect)) {
        return FALSE;
    }
    vtable[1] = hook;
    FlushInstructionCache(GetCurrentProcess(), &vtable[1], sizeof(hook));
    DWORD dummy = 0;
    VirtualProtect(&vtable[1], sizeof(hook), oldProtect, &dummy);

    InterlockedExchange(&stageCompatApplied, 1);
    return TRUE;
}

static BOOL ApplyPqMoveInventoryItemRead(uintptr_t base) {
    if (InterlockedCompareExchange(&moveInventoryReadApplied, 0, 0) != 0) {
        return TRUE;
    }

    DWORD* vtable = (DWORD*)(base + moveInventoryVTableOffset);
    if (!IsValidPointer(vtable)) {
        return FALSE;
    }

    DWORD oldEntry1 = 0;
    __try {
        oldEntry1 = vtable[1];
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        return FALSE;
    }

    if (oldEntry1 < (DWORD)base || oldEntry1 > (DWORD)(base + 0x08000000)) {
        return FALSE;
    }

    originalMoveInventoryItemRead = (PacketDeserializeFunc)(uintptr_t)oldEntry1;

    DWORD hook = (DWORD)(uintptr_t)&HookedPqMoveInventoryItemRead;
    DWORD oldProtect = 0;
    if (!VirtualProtect(&vtable[1], sizeof(hook), PAGE_EXECUTE_READWRITE, &oldProtect)) {
        return FALSE;
    }
    vtable[1] = hook;
    FlushInstructionCache(GetCurrentProcess(), &vtable[1], sizeof(hook));
    DWORD dummy = 0;
    VirtualProtect(&vtable[1], sizeof(hook), oldProtect, &dummy);

    InterlockedExchange(&moveInventoryReadApplied, 1);
    return TRUE;
}

static int __cdecl HookedOpenExteriorCellMask(unsigned int cell) {
    unsigned int cell8 = (unsigned int)((BYTE)cell);
    switch (cell8) {
        case 36u:
            return 1;
        case 37u:
            return 2;
        case 38u:
            return 4;
        case 44u:
            return 8;
        default:
            return 0;
    }
}

static BOOL ApplyOpenExteriorCellMaskCompat(uintptr_t base) {
    if (InterlockedCompareExchange(&openExteriorCellMaskCompatApplied, 0, 0) != 0) {
        return TRUE;
    }

    BYTE* fn = (BYTE*)(base + openExteriorCellMaskOffset);
    if (!IsValidPointer(fn)) {
        return FALSE;
    }

    DWORD oldProtect = 0;
    if (!VirtualProtect(fn, 8u, PAGE_EXECUTE_READWRITE, &oldProtect)) {
        return FALSE;
    }

    BYTE oldBytes[8];
    __try {
        memcpy(oldBytes, fn, sizeof(oldBytes));
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        DWORD dummyProtect = 0;
        VirtualProtect(fn, 8u, oldProtect, &dummyProtect);
        return FALSE;
    }

    if (!(oldBytes[0] == 0x55 && oldBytes[1] == 0x8B && oldBytes[2] == 0xEC)) {
        DWORD dummyProtect = 0;
        VirtualProtect(fn, 8u, oldProtect, &dummyProtect);
        return FALSE;
    }

    intptr_t rel = (intptr_t)(void*)&HookedOpenExteriorCellMask - ((intptr_t)fn + 5);
    if (rel < (-2147483647LL - 1LL) || rel > 2147483647LL) {
        DWORD dummyProtect = 0;
        VirtualProtect(fn, 8u, oldProtect, &dummyProtect);
        return FALSE;
    }

    fn[0] = 0xE9;
    *(LONG*)(fn + 1) = (LONG)rel;
    fn[5] = 0x90;
    fn[6] = 0x90;
    fn[7] = 0x90;

    FlushInstructionCache(GetCurrentProcess(), fn, 8u);
    DWORD dummy = 0;
    VirtualProtect(fn, 8u, oldProtect, &dummy);

    InterlockedExchange(&openExteriorCellMaskCompatApplied, 1);
    return TRUE;
}

static BOOL ApplyNpcCompat(uintptr_t base) {
    if (InterlockedCompareExchange(&npcCompatApplied, 0, 0) != 0) {
        return TRUE;
    }

    DWORD* vtblAdd = (DWORD*)(base + pcAddNpcVTableOffset);
    DWORD* vtblUpd = (DWORD*)(base + pcUpdateNpcVTableOffset);
    if (!IsValidPointer(vtblAdd) || !IsValidPointer(vtblUpd)) {
        return FALSE;
    }

    DWORD oldAdd = 0;
    DWORD oldUpd = 0;
    __try {
        oldAdd = vtblAdd[2];
        oldUpd = vtblUpd[2];
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        return FALSE;
    }

    if (oldAdd < (DWORD)base || oldAdd > (DWORD)(base + 0x08000000) ||
        oldUpd < (DWORD)base || oldUpd > (DWORD)(base + 0x08000000)) {
        return FALSE;
    }

    originalPcAddNpcWrite = (PacketSerializeFunc)(uintptr_t)oldAdd;
    originalPcUpdateNpcWrite = (PacketSerializeFunc)(uintptr_t)oldUpd;

    packetSerializeBase = (PacketSerializeBaseFunc)(base + packetSerializeBaseOffset);
    packetWriteVec3 = (PacketWriteVec3Func)(base + packetWriteVec3Offset);
    packetWriteVecArray1C = (PacketWriteVecArray1CFunc)(base + packetWriteVecArray1COffset);
    openPacketStringNode = (OpenPacketStringNodeFunc)(base + openPacketStringNodeOffset);

    DWORD hookAdd = (DWORD)(uintptr_t)&HookedPcAddNpcWrite;
    DWORD hookUpd = (DWORD)(uintptr_t)&HookedPcUpdateNpcWrite;

    DWORD oldProtect = 0;
    if (!VirtualProtect(&vtblAdd[2], sizeof(DWORD), PAGE_EXECUTE_READWRITE, &oldProtect)) {
        return FALSE;
    }
    vtblAdd[2] = hookAdd;
    FlushInstructionCache(GetCurrentProcess(), &vtblAdd[2], sizeof(DWORD));
    DWORD dummy = 0;
    VirtualProtect(&vtblAdd[2], sizeof(DWORD), oldProtect, &dummy);

    if (!VirtualProtect(&vtblUpd[2], sizeof(DWORD), PAGE_EXECUTE_READWRITE, &oldProtect)) {
        return FALSE;
    }
    vtblUpd[2] = hookUpd;
    FlushInstructionCache(GetCurrentProcess(), &vtblUpd[2], sizeof(DWORD));
    VirtualProtect(&vtblUpd[2], sizeof(DWORD), oldProtect, &dummy);

    InterlockedExchange(&npcCompatApplied, 1);
    return TRUE;
}

static BOOL ApplyAllPacketHooks(void) {
    HMODULE exe = GetModuleHandleW(NULL);
    if (!exe) {
        return FALSE;
    }
    uintptr_t base = (uintptr_t)exe;

    BOOL moveInventoryDirectInitDone = ApplyMoveInventoryDirectApply(base);
    BOOL slotTypeCompatDone = ApplyMoveInventorySlotTypeCompat(base);
    BOOL stageDone = ApplyPqChangeStageCompat(base);
    BOOL moveInventoryDone = ApplyPqMoveInventoryItemRead(base);
    BOOL openExteriorMaskDone = ApplyOpenExteriorCellMaskCompat(base);
    BOOL npcDone = ApplyNpcCompat(base);

    return moveInventoryDirectInitDone &&
           slotTypeCompatDone &&
           stageDone &&
           moveInventoryDone &&
           openExteriorMaskDone &&
           npcDone;
}

static MiniDumpWriteDumpFunc GetOriginalMiniDumpWriteDump(void) {
    if (realMiniDumpWriteDump) {
        return realMiniDumpWriteDump;
    }

    wchar_t sysDir[MAX_PATH];
    UINT n = GetSystemDirectoryW(sysDir, MAX_PATH);
    if (n == 0 || n > (MAX_PATH - 13)) {
        return NULL;
    }

    wcscat_s(sysDir, MAX_PATH, L"\\dbghelp.dll");
    HMODULE real = LoadLibraryW(sysDir);
    if (!real) {
        return NULL;
    }

    realMiniDumpWriteDump = (MiniDumpWriteDumpFunc)GetProcAddress(real, "MiniDumpWriteDump");
    return realMiniDumpWriteDump;
}

extern "C" BOOL WINAPI MiniDumpWriteDump(
    HANDLE hProcess,
    DWORD ProcessId,
    HANDLE hFile,
    MINIDUMP_TYPE DumpType,
    PMINIDUMP_EXCEPTION_INFORMATION ExceptionParam,
    PMINIDUMP_USER_STREAM_INFORMATION UserStreamParam,
    PMINIDUMP_CALLBACK_INFORMATION CallbackParam) {

    MiniDumpWriteDumpFunc fn = GetOriginalMiniDumpWriteDump();
    if (!fn) {
        SetLastError(ERROR_PROC_NOT_FOUND);
        return FALSE;
    }

    return fn(hProcess, ProcessId, hFile, DumpType, ExceptionParam, UserStreamParam, CallbackParam);
}

static DWORD WINAPI InitThreadProc(LPVOID lpParam) {
    (void)lpParam;

    for (int i = 0; i < 200; ++i) {
        if (ApplyAllPacketHooks()) {
            return 0;
        }
        Sleep(100);
    }
    return 0;
}

BOOL APIENTRY DllMain(HMODULE hModule, DWORD reason, LPVOID reserved) {
    (void)reserved;

    if (reason == DLL_PROCESS_ATTACH) {
        DisableThreadLibraryCalls(hModule);
        HANDLE hThread = CreateThread(NULL, 0, InitThreadProc, NULL, 0, NULL);
        if (hThread) {
            CloseHandle(hThread);
        }
    }

    return TRUE;
}
