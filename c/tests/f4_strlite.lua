-- F4-lite held-out validation (abstractions/pilot/SUITE.md H1-H5):
-- string literals, concatenation (with integer coercion), length,
-- byte-lexicographic order, and arithmetic on integer-valued strings
local a = "lua"
local b = "5.4"
local n = 7
print(a, b)
print(a .. " " .. b, a .. n, n .. n)
print(#a, #(a .. b), #"")
print(a < b, b < a, a <= "lua", "abc" < "abd", "" < "a", "Z" < "a")
print("10" + 1, -"2", "6" * "7", "10" // 3, "7" % 2)
local s = ""
for i = 1, 5 do s = s .. i end
print(s, #s, s + 0)
print(a == "lua", a ~= b)
