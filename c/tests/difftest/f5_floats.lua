-- floats and %.14g formatting (soft-float on rv64i)
print(1 / 3, 0.1 + 0.2, 1e100, 2 ^ 53, 2 ^ 63, -0.0, 1 / 0, -1 / 0)
print(3 / 2, 7 // 2.0, 7 % 2.5, -7 % 2.5, 3.0 == 3, 1e15, 1e16, 123456789012345.0)
print(10 / 4, 2 ^ 0.5, 100000000000000)
print(string.format("%.3f %g %e %5.1f", 3.14159, 1e-5, 12345.678, 2.25))
print(tostring(1e300 * 1e10), 0/0 ~= 0/0)
print(7.0 // 0.0, -7 // 0.0, 5 // 0.0 == 1/0)
print(math_floor, 3.7 // 1, -3.7 // 1, tonumber("1e2"), tonumber(".5"))
local s = 0.0
for i = 1, 10 do s = s + 0.1 end
print(s, s == 1.0)
for x = 1.0, 2.0, 0.25 do io = x end
print(io)
