import z3
from n_queens import n_queens

n_queens = n_queens(20)


vars = []
for i in range(n_queens.n):
    vars.append(z3.Int(f'row_{i}'))
print(vars)
s = z3.Solver()

for i in range(n_queens.n):
    for j in range(n_queens.n):
        if(i != j):
            s.add(vars[i] >= 0)
            s.add(vars[i] < n_queens.n)
            s.add(vars[i] != vars[j])
            s.add(z3.Abs(vars[i] - vars[j]) != z3.Abs(i - j))


solution = s.check()
print(solution)
if solution == z3.sat:
    model = s.model()
    for i in range(n_queens.n):
        n_queens.state[i][model[vars[i]].as_long()] = 1
    n_queens.print_grid()
else:
    print("No solution found.")