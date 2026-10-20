-- float loops and accumulation with `/` and `^`
local s = 0.0
for i = 1, 2, 0.25 do s = s + i / 4 end
print(s)
for x = 0.5, 2 do print(x, x ^ 2, x ^ 0.5, 1 / x) end
local h = 1.0
while h > 1e-3 do h = h / 10 end
print(h, h * 1000 == 1)
