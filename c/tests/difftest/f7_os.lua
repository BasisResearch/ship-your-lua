-- F7: the os library with the frozen clock (htif.c's _gettimeofday/_times;
-- the host lua gets the same clock from c/src/baremetal.h, and runs with
-- TZ=UTC0 and an empty environment, as the ELF does)
print(os.time(), os.clock(), os.difftime(os.time(), 0))
print(os.date("!%Y-%m-%d %H:%M:%S"), os.date("%Y-%m-%d %H:%M:%S", 86400 * 365))
local t = os.date("!*t", 1000000000)
print(t.year, t.month, t.day, t.hour, t.min, t.sec, t.wday, t.yday, t.isdst)
print(os.date("!%A %B %j %p %%", 1234567890))
print(os.time({year = 2000, month = 1, day = 1, hour = 0}))
print(os.time({year = 2024, month = 2, day = 30, hour = 12, min = 30}))
print(pcall(os.date, "%Ez"))
print(os.getenv("HOME"), os.getenv("F7_NOT_SET"))
print(pcall(os.time, {year = 2000}))

-- os.exit with a code: buffered output is flushed first
io.write("exiting with 3\n")
io.write("buffered, ", "flushed by exit\n")
os.exit(3)
print("unreachable")
