-- F1 source constructs beyond f1_ops.lua, for Layer B translation
-- validation: if/elseif/else, repeat-until seeing the body's locals,
-- break out of while/for/repeat (also from inside an if), block scoping
-- and shadowing, multiple locals with missing and extra values
local a, b, c = 1, 2
local d
print(a, b, c, d)
local e = 3, 4
print(e)
local t = 0
for i = 1, 20 do
  if i % 3 == 0 then
    t = t + i
  elseif i % 5 == 0 then
    t = t - i
  else
    t = t + 1
  end
  if i >= 15 then break end
end
print(t)
local x = 10
local y = 0
while true do
  local x = x - y
  y = y + 2
  if x < 5 then
    print(x)
    break
  end
end
print(x, y)
local n = 0
repeat
  local m = n * 2
  n = n + 1
until m >= 6 or n > 100
print(n)
local k = 0
repeat
  k = k + 1
  if k == 4 then break end
until false
print(k)
local s = 0
for i = 5, 1, -1 do
  for j = i, 5 do
    if j == 4 then break end
    s = s + j
  end
end
print(s)
if not (s > 100) and s ~= 0 then print(true) else print(false) end
local v = nil
if v then print(1) elseif v == false then print(2) else print(3) end
local w = 7
print(w // 2, -w % 3, w > 5 and w or 0, (w < 5) or nil)
