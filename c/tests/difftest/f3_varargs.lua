-- F3: varargs, multiple returns, select, tail calls
local function va(...) return select('#', ...), ... end
print(va())
print(va(1, nil, 3))
local function mr() return 1, 2, 3 end
print(mr(), mr())
print((mr()))
local t = {mr(), mr()}
print(#t)
print(select(2, "a", "b", "c"), select(-1, "a", "b", "c"))
local function loop(n, acc) if n == 0 then return acc end return loop(n - 1, acc + n) end
print(loop(10000, 0))
local function sum(...) local s = 0 for _, v in ipairs({...}) do s = s + v end return s end
print(sum(1, 2, 3, 4, 5))
