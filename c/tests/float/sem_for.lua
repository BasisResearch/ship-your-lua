local zero = 0.0 local nan = zero / zero local big = 1e308 local ten = 10 local inf = big * ten local mi = -9223372036854775807 - 1
local a, b, s, t = 0, 0, 0, 0
print("loop 1")
for i = 0.5, 3 do print(i) end
print("loop 2")
for i = 1, 2, 0.25 do print(i) end
print("loop 3")
for i = 3, 1, -0.5 do print(i) end
print("loop 4")
for i = 1.0, 3 do print(i) end
print("loop 5")
for i = 1, 3, 1.0 do print(i) end
print("loop 6")
for i = 0.1, 1, 0.1 do print(i) end
print("loop 7")
for i = 1, 3.7 do print(i) end
print("loop 8")
for i = 3, 1.2, -1 do print(i) end
print("loop 9")
for i = -1, -3.5, -1 do print(i) end
print("loop 10")
for i = 1, 0 do print(i) end
print("loop 11")
for i = 1, -inf do print(i) end
print("loop 12")
for i = 1, inf do print(i) if i >= 4 then break end end
print("loop 13")
for i = 1.0, inf do print(i) if i >= 4 then break end end
print("loop 14")
for i = 1, nan do print(i) end
print("loop 15")
for i = 1, nan, -1 do print(i) if i < -2 then break end end
print("loop 16")
for i = 1.0, nan do print(i) end
print("loop 17")
for i = nan, 3 do print(i) end
print("loop 18")
for i = "1", 3 do print(i) end
print("loop 19")
for i = 1, "3" do print(i) end
print("loop 20")
for i = 1, 3, "1" do print(i) end
print("loop 21")
for i = "0x10", 18 do print(i) end
print("loop 22")
for i = " 2 ", "4.5" do print(i) end
print("loop 23")
for i = 9223372036854775800, 1e300 do print(i) end
print("loop 24")
for i = mi + 3, -1e300, -1 do print(i) end
print("loop 25")
for i = 9223372036854775806, 9223372036854775807 do print(i) end
print("loop 26")
for i = mi, mi + 2 do print(i) end
print("loop 27")
for i = 1, 9223372036854775807, 4611686018427387904 do print(i) end
print("loop 28")
for i = 9007199254740990.0, 9007199254740994.0, 2 do print(i) end
print("loop 29")
for i = 9007199254740991, 9007199254740994.0 do print(i) end
print("loop 30")
for i = 1e308, inf, 1e308 do print(i) if i > 1e308 then break end end
print("loop 31")
for i = -0.0, 1 do print(i) end
print("loop 32")
for i = 0, -0.0 do print(i) end
print("loop 33")
for i = 1, 3 do for j = i, 3, 0.5 do print(i, j) end end
print("loop 34")
for i = 3, 1, -1 do for j = 1.5, i do print(i * j, i // j, i % j) end end
print("loop 35")
for i = 1, 2 do local x = i * 0.5 while x < 2 do print(x) x = x + 0.75 end end
print("loop 36")
for i = 2.5, 1, -0.5 do if i == 2 then print("two", i) elseif i < 2 then print("lt", i) end end
