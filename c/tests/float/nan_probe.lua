-- NaN probe: the bits of the NaNs the ELF's soft-float produces.
-- Inputs are built from bit patterns so that luac cannot constant-fold.
local function B(x) return (string.unpack("<i8", string.pack("<d", x))) end
local function F(i) return (string.unpack("<d", string.pack("<i8", i))) end
local z, one, inf = F(0), F(0x3ff0000000000000), F(0x7ff0000000000000)
local pnan = F(0x7ff0000000000123)          -- signalling NaN with payload
local nnan = F(-0x0007ffffffffff00)         -- 0xfff8000000000100: negative quiet NaN, payload
print(B(z / z), B(-(z / z)), B(one % z), B(inf - inf), B(z * inf))
print(B(pnan + one), B(nnan + one), B(nnan * one), B(nnan / one), B(one % nnan))
print(z / z, -(z / z), nnan)
