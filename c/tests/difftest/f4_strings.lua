-- F4: strings and the string library
local s = "Hello, " .. "Lua" .. " " .. 5 .. 4
print(s, #s)
print(s:upper(), s:lower(), s:sub(1, 5), s:sub(-3), s:rep(2, "|"))
print(string.byte("A"), string.char(72, 105), ("abc"):reverse())
print(string.format("%d %5d %-5d| %x %X %o %s %q", 42, 7, 7, 255, 255, 8, "str", "a\nb"))
print(("x = %s, y = %s"):format(nil, true))
print(string.find("hello world", "o w"), string.find("hello", "l+"))
print(string.match("key=value", "(%w+)=(%w+)"))
print(string.gsub("hello world", "o", "0"))
for w in string.gmatch("one two three", "%a+") do print(w) end
print(tostring(10) == "10", tonumber("0x10"), tonumber("  12  "), tonumber("z", 36))
print("10" + 5, "3" * "4", 10 .. 20)
print("a" < "b", "abc" < "abd", "" < "a")
