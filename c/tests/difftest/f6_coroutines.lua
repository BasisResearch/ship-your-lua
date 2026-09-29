-- coroutines (later fragment)
local co = coroutine.create(function(a, b)
  local c = coroutine.yield(a + b)
  local d, e = coroutine.yield(c * 2)
  return d + e
end)
print(coroutine.resume(co, 1, 2))
print(coroutine.resume(co, 10))
print(coroutine.resume(co, 3, 4))
print(coroutine.resume(co))
print(coroutine.status(co))
local gen = coroutine.wrap(function() for i = 1, 5 do coroutine.yield(i * i) end end)
local out = {}
for _ = 1, 5 do out[#out + 1] = gen() end
print(table.concat(out, " "))
print(pcall(coroutine.wrap(function() error("in co", 0) end)))
