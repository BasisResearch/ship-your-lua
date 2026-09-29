-- F1: integer arithmetic, wraparound, floor division/modulo, bitwise, compare
local a, b = 7, -3
print(a + b, a - b, a * b, a // b, a % b, -a // 2, -a % 2)
print(type(print), type(nil), type(2), type(2.0))
local big = 9223372036854775807
print(big + 1, big * 2, -big - 1)
print((-9223372036854775807 - 1) // -1)
print(5 & 3, 5 | 3, 5 ~ 3, ~5, 1 << 62, 1 << 63, 1 << 64, -1 >> 1)
print(3 < 4, 3 <= 3, 4 > 5, 2 == 2, 2 ~= 2)
local x = 0
for i = 1, 100 do x = x + i * i end
print(x)
