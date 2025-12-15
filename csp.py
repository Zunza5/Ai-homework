import z3
from n_queens import n_queens
import time

class z3_solver:

    def __init__(self, problem):
        self.problem = problem
        self.vars = []
        self.time_taken = 0
        for i in range(problem.n):
            self.vars.append(z3.Int(f'row_{i}'))
        self.s = z3.Solver()
        for i in range(problem.n):
            for j in range(problem.n):
                if(i != j):
                    self.s.add(self.vars[i] >= 0)
                    self.s.add(self.vars[i] < problem.n)
                    self.s.add(self.vars[i] != self.vars[j])
                    self.s.add(z3.Abs(self.vars[i] - self.vars[j]) != z3.Abs(i - j))
    
    def print_solution(self):
        start_time = time.time()
        solution = self.s.check()
        print(solution)
        self.time_taken = time.time() - start_time
        if solution == z3.sat:
            model = self.s.model()
            for i in range(n_queens.n):
                n_queens.state[i][model[self.vars[i]].as_long()] = 1
            n_queens.print_grid()
        else:
            print("No solution found.")

if __name__ == '__main__':
    queens = n_queens(20)
    csp_solver = z3_solver(queens)
    csp_solver.print_solution()