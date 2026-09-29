/* Linker script for bare-metal RISC-V (copied from ship-your-interpreter's
 * c/src/link.ld; the .lua_chunk region is new).
 * Originally for the QEMU `virt` machine.
 * RAM starts at 0x80000000; QEMU loads the ELF at its link address
 * when started with `-bios none -kernel while-riscv.elf`. */
OUTPUT_ARCH(riscv)
ENTRY(_start)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 128M
}

__stack_size = 8M;

SECTIONS
{
    .text : {
        *(.text.init)
        *(.text .text.*)
    } > RAM

    .rodata : ALIGN(8) {
        *(.rodata .rodata.*)
        *(.srodata .srodata.*)
    } > RAM

    /* HTIF mailbox (tohost/fromhost); HTIF hosts such as Spike and the
     * sail-riscv emulators find it via the section name. Empty in the
     * semihosting build. */
    .tohost : ALIGN(64) {
        *(.tohost)
    } > RAM

    .data : ALIGN(8) {
        __global_pointer$ = . + 0x800;
        *(.data .data.*)
        *(.sdata .sdata.*)
    } > RAM

    .bss : ALIGN(8) {
        __bss_start = .;
        *(.sbss .sbss.*)
        *(.bss .bss.*)
        *(COMMON)
        . = ALIGN(8);
        __bss_end = .;
    } > RAM

    /* The embedded Lua chunk (src/chunk.S), in a fixed 64 KiB region after
     * .bss: .text/.rodata/.data/.bss and _end (the heap start) are then
     * the same bytes and addresses for every chunk, so one image pin
     * serves every program. Not zeroed by crt0 (it is not in .bss). */
    .lua_chunk : ALIGN(8) {
        __chunk_region = .;
        KEEP(*(.lua_chunk))
        ASSERT(. - __chunk_region <= 0x10000, "Lua chunk larger than 64 KiB");
        . = __chunk_region + 0x10000;
    } > RAM

    . = ALIGN(16);
    _end = .;
    PROVIDE(end = .);

    __stack_top = ORIGIN(RAM) + LENGTH(RAM);
    __heap_end = __stack_top - __stack_size;
}
