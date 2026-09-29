-- F1: conditionals, and/or/not, nested loops, repeat-until
local function classify(n)
  if n < 0 then return -1 elseif n == 0 then return 0 else return 1 end
end
print(classify(-5), classify(0), classify(42))
print(nil or 3, false and 1, 1 and 2, not nil, not 0)
local i, t = 0, 0
repeat i = i + 1; t = t + i until i >= 10
print(i, t)
local primes = 0
for n = 2, 200 do
  local p = true
  local d = 2
  while d * d <= n do
    if n % d == 0 then p = false; break end
    d = d + 1
  end
  if p then primes = primes + 1 end
end
print(primes)
