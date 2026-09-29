-- F2: real `next`/pairs order over the hash part (fixed hash seed)
local t = {}
for _, k in ipairs({"alpha", "beta", "gamma", "delta", "eps", "zeta", "eta", "theta"}) do
  t[k] = #k
end
t[1] = "one"; t[2] = "two"; t[100] = "hundred"; t[-7] = "neg"; t[2.5] = "float"
t[true] = "yes"
for k, v in pairs(t) do print(k, v) end
local n = 0
for k in next, t do n = n + 1 end
print(n)
t.alpha = nil
local keys = {}
for k in pairs(t) do keys[#keys + 1] = tostring(k) end
print(table.concat(keys, ","))
