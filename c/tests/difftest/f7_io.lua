-- F7: the io library over htif.c's in-image file system (host: real files
-- in the working directory; every file is removed at the end)
local A, B = "f7_io_a.txt", "f7_io_b.txt"

-- write, then read back in every format
local f = assert(io.open(A, "w"))
print(io.type(f), io.type(io.stdout), io.type(42))
print(f:write("line one\n", "line two\n", 42, " ", 3.5, "\n") == f)
f:write("tail without newline")
print(f:seek("cur"), f:seek("end"), f:seek("set", 5))
f:close()
print(io.type(f), pcall(f.write, f, "x"))

f = assert(io.open(A, "r"))
print(f:read("l"))
print(f:read("L"))
print(f:read("n", "n"))
print(f:read(4), f:read(0))
print(f:read("a"))
print(f:read("a"), f:read("l"), f:read(0))
print(f:seek("set", 9), f:read(8), f:seek("cur"), f:seek("end", -7), f:read("a"))
f:close()

-- io.lines and file:lines
local n = 0
for l in io.lines(A) do n = n + 1; print(n, l) end
for a, b in io.lines(A, 4, "l") do print(a, b) end
f = assert(io.open(A))
for l in f:lines("L") do io.write("[", l, "]") end
print()
f:close()

-- append and update modes, truncation
f = assert(io.open(B, "a")); f:write("abc"); f:close()
f = assert(io.open(B, "a+")); f:write("def"); f:seek("set"); print(f:read("a")); f:close()
f = assert(io.open(B, "r+")); f:write("XY"); f:seek("set", 0); print(f:read("a")); f:close()
f = assert(io.open(B, "w+")); print(f:read("a"), f:seek("end")); f:write("new"); f:close()
f = assert(io.open(B, "rb")); print(f:read("a")); f:close()

-- seek past the end fills with zeros
f = assert(io.open(B, "w")); f:seek("set", 4); f:write("z"); f:close()
f = assert(io.open(B)); print(string.byte(f:read("a"), 1, -1)); f:close()

-- default input/output redirection
io.output(B); io.write("via io.write\n", 7, "\n"); io.close(); io.output(io.stdout)
io.input(B); print(io.read("l"), io.read("n")); io.close(io.input()); io.input(io.stdin)
print(io.read("a") == "", io.read("l"))

-- errors: message and errno as the OS spec gives them
print(io.open("f7_io_missing.txt"))
print(io.open("f7_io_missing.txt", "r+"))
print(pcall(io.open, A, "rw"))
print(pcall(io.lines, "f7_io_missing.txt"))
print(os.remove("f7_io_missing.txt"))
print(os.rename("f7_io_missing.txt", "f7_io_c.txt"))

-- remove and rename
print(os.rename(A, "f7_io_c.txt"))
print(io.open(A))
f = assert(io.open("f7_io_c.txt")); print(f:read("l")); f:close()
print(os.rename(B, "f7_io_c.txt"))
f = assert(io.open("f7_io_c.txt")); print(f:read("l")); f:close()
print(os.remove("f7_io_c.txt"))
print(io.open("f7_io_c.txt"))
print(os.remove(B))

-- a removed file stays readable through an open handle
f = assert(io.open(A, "w+")); f:write("still here"); print(os.remove(A))
f:seek("set"); print(f:read("a")); f:close()
print(io.open(A))
