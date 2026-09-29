-- F1-only: numeric for (FORPREP/FORLOOP), floor div/mod, wraparound,
-- comparisons, and/or (TESTSET), not, equality with nil/booleans
local s = 0
for i = 1, 10 do s = s + i * i end
print(s)
for i = 10, 1, -3 do print(i) end
for i = 1, 0 do print(i) end
local a, b = 7, -3
print(a // b, a % b, -a // 2, -a % 2, a // -1, 0 - a)
local big = 9223372036854775807
print(big + 1, big * 2, -big - 1)
print((-9223372036854775807 - 1) // -1, (-9223372036854775807 - 1) % -1)
local x = nil
local y = x or 5
local z = y and 6
print(y, z, not x, not y, x == nil, y == 5, z ~= 6)
local n = 0
for i = 9223372036854775800, 9223372036854775807 do n = n + 1 end
print(n, 3 < 4, 4 <= 3, 5 > 2, 5 >= 6)
local c = 0
local k = 1
while k < 1000 do k = k * 3 c = c + 1 end
print(c, k, true, false)
