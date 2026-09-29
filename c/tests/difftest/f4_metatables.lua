-- F4: metatables and metamethods
local V = {}
V.__index = V
V.__add = function(a, b) return setmetatable({x = a.x + b.x}, V) end
V.__eq = function(a, b) return a.x == b.x end
V.__lt = function(a, b) return a.x < b.x end
V.__le = function(a, b) return a.x <= b.x end
V.__tostring = function(a) return "V(" .. a.x .. ")" end
V.__len = function(a) return a.x end
V.__concat = function(a, b) return tostring(a) .. "&" .. tostring(b) end
V.__call = function(self, y) return self.x * y end
function V.new(x) return setmetatable({x = x}, V) end
function V:double() return V.new(self.x * 2) end
local a, b = V.new(3), V.new(4)
print(tostring(a + b), a == b, a < b, a <= b, #a, a .. b, a(10))
print(tostring(a:double()))
local defaults = setmetatable({}, {__index = function(t, k) return k .. "!" end})
print(defaults.foo, rawget(defaults, "foo"))
local log = {}
local proxy = setmetatable({}, {__newindex = function(t, k, v) log[#log + 1] = k; rawset(t, k, v) end})
proxy.a = 1; proxy.b = 2; proxy.a = 3
print(table.concat(log, ","), proxy.a)
print(getmetatable("abc").__index == string)
