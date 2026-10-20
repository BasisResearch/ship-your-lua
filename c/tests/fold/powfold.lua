-- `luac` folds a constant `^` with the host's libm `pow` (glibc); the ELF's
-- runtime `^` is newlib's. 0.5 ^ -0.5: glibc 1.4142135623730951, newlib
-- 1.4142135623730949 (FLOAT-DESIGN.md §5 R5)
local a, b = 0.5, -0.5
print(0.5 ^ -0.5 == a ^ b)
