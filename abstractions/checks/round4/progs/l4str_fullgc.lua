-- Round 4, L4-str: a full collection (collectgarbage, a CALL) with short and
-- long strings live in registers and K, then F1 uses of them.
local keep = "a short string held in a register"
local long1 = string.rep("long string body ", 4)
local long2 = string.rep("long string body ", 4)
local s = "x" .. 1
collectgarbage()
collectgarbage()
print(keep, s, long1 == long2, #long1, long1 < keep, keep <= long2)
