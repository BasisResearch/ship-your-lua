-- Lua port of ship-your-interpreter c/tests/while.wl
-- while loops, break, continue (goto), nesting
local i = 0
local sum = 0
while i < 10 do
  i = i + 1
  sum = sum + i
end
print(sum)

local n = 0
local total = 0
while true do
  n = n + 1
  if n > 100 then break end
  if n % 2 == 0 then goto continue end
  total = total + n
  ::continue::
end
print(total)

local acc = 0
local a = 1
while a <= 3 do
  local b = 1
  while b <= 3 do
    acc = acc + a * b
    b = b + 1
  end
  a = a + 1
end
print(acc)
