-- Round 4, L4-str stress: strings held in registers and K (short and long)
-- across enough allocation to run the collector, long-string equality
-- (luaS_eqlngstr -> memcmp) and order (l_strcmp).
local keep = "a short string held in a register"
local long1 = "a long string, longer than LUAI_MAXSHORTLEN = 40 bytes, held in a register"
local long2 = "a long string, longer than LUAI_MAXSHORTLEN = 40 bytes, held in a register"
local s = ""
local t = {}
for i = 1, 3000 do
  s = "garbage " .. i
  if i % 100 == 0 then t[#t + 1] = s end
end
print(keep, s, #t, long1 == long2, long1 < keep, keep <= long2)
print(collectgarbage("count") > 0, long1 == long2, keep)
