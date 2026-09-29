-- F2: table library
local t = {5, 3, 8, 1, 9, 2}
table.sort(t)
print(table.concat(t, " "))
table.sort(t, function(a, b) return a > b end)
print(table.concat(t, " "))
table.insert(t, 7); table.insert(t, 1, 0)
print(table.concat(t, ","), #t)
print(table.remove(t), table.remove(t, 1), #t)
print(table.unpack({1, 2, 3}))
local p = table.pack(1, nil, 3)
print(p.n, p[1], p[2], p[3])
print(table.concat(table.move({1, 2, 3}, 1, 3, 2, {9}), ","))
