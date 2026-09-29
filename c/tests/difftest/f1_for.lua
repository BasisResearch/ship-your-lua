-- F1: numeric for (FORPREP/FORLOOP) edge cases
local s = 0
for i = 10, 1, -1 do s = s * 2 + i end
print(s)
local c = 0
for i = 1, 0 do c = c + 1 end
print(c)
for i = 1, 10, 3 do io = i end
print(io)
local n = 0
for i = 9223372036854775800, 9223372036854775807 do n = n + 1 end
print(n)
for i = -3, 3, 2 do print(i) end
local ok, err = pcall(function() for i = 1, 10, 0 do end end)
print(ok, err ~= nil)
