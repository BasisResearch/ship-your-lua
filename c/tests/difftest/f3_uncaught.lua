-- F3: uncaught runtime error -> nonzero exit on both sides
print("before")
local t = nil
print(t.field)
print("unreachable")
