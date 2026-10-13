-- brk_hi probe: allocations of growing size, each forcing malloc_extend_top
local t = {}
for _, n in ipairs({100, 1000, 4000, 4096, 5000, 8000, 12000, 16384, 20000, 50000, 65536, 100000, 300000, 1000000}) do
  t[#t + 1] = string.rep("x", n)
end
print(#t)
