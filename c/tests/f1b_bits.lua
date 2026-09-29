-- F1 + F1b only (integer bitwise): register, constant (BANDK/BORK/BXORK)
-- and immediate (SHRI/SHLI) forms, luaV_shiftl's edge cases (shift >= 64
-- gives 0, a negative shift goes the other way, shifts are logical), the
-- swapped operand of SHLI (sC << R[B]), and BNOT. No strings but `print`,
-- no floats.
local a, b = 0x5A5A, 0x0FF0
print(a & b, a | b, a ~ b, ~a, ~0)
print(a & 0xFF, a | 0x100, a ~ 0xFFFF, -1 & 0x7FFFFFFFFFFFFFFF)
local m = -1
print(m >> 1, m >> 63, m << 63, a >> 4, a << 4)
local s = 64
local n = -3
local z = -9223372036854775807 - 1
print(a << s, a >> s, m >> s, a << n, a >> n, 1 << z, m >> z)
local t = 5
print(3 << t, 3 << a, 1 << b, 0x700 << n, 1 << s, 5 << m, -8 << m)
local acc = 0
for i = 0, 62, 7 do acc = acc | (1 << i) end
print(acc, acc >> 49, acc & ~0x81)
local h = 0
for i = 1, 20 do h = ((h << 5) ~ (h >> 2) ~ i) & 0xFFFFFF end
print(h, (h ~ h) == 0, ~~h == h)
