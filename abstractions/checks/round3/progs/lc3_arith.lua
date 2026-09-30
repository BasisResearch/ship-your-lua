-- MUL/MULK/MOD/MODK/IDIV/IDIVK and FORPREP with step ~= 1 (soft-int helpers)
local x, y = 123456789, -9876
print(x * y, x * 3, x % y, x % 7, x // y, x // -7, y % 5, y // 5)
local big = 9223372036854775807
print(big * big, (-big) // 3, big % -10)
local s = 0
for i = 1, 100, 7 do s = s + i end
for i = 50, -50, -9 do s = s + i end
for i = -3, 4000000000, 999999999 do s = s + 1 end
print(s)
