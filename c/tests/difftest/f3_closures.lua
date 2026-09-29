-- F3: closures, shared upvalues, recursion
local function counter()
  local c = 0
  return function() c = c + 1; return c end, function() return c end
end
local inc, get = counter()
inc(); inc(); inc()
print(get())
local fs = {}
for i = 1, 3 do fs[i] = function() return i * 10 end end
print(fs[1](), fs[2](), fs[3]())
local function fib(n) if n < 2 then return n end return fib(n - 1) + fib(n - 2) end
print(fib(15))
local function compose(f, g) return function(...) return f(g(...)) end end
print(compose(function(x) return x + 1 end, function(x, y) return x * y end)(6, 7))
