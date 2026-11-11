/* vita-elf-create appends the module's SCE data (module info, import tables)
 * right after the text segment and fails when the data segment, which
 * VitaSDK's armelf.x puts at the next 64 KB boundary, starts too close.
 * Skipping past the next boundary first guarantees room. No section covers the
 * gap, so it costs address space, not memory. (Same fix as the Fury3 port.) */
SECTIONS
{
  . = ALIGN(0x10000) + 0xF000;
}
INSERT AFTER .eh_frame;
