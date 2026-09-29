-- F4: small OO program: inheritance through __index chains, string keys
local Animal = {}
Animal.__index = Animal
function Animal.new(name, sound) return setmetatable({name = name, sound = sound}, Animal) end
function Animal:speak() return self.name .. " says " .. self.sound end
local Dog = setmetatable({}, {__index = Animal})
Dog.__index = Dog
function Dog.new(name) local d = Animal.new(name, "woof"); return setmetatable(d, Dog) end
function Dog:fetch() return self.name .. " fetches" end
local d = Dog.new("Rex")
print(d:speak(), d:fetch())
local words = {}
for w in ("the quick brown fox jumps over the lazy dog the end"):gmatch("%a+") do
  words[w] = (words[w] or 0) + 1
end
local ks = {}
for k in pairs(words) do ks[#ks + 1] = k end
table.sort(ks)
for _, k in ipairs(ks) do io = k print(k, words[k]) end
