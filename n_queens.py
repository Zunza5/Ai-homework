class n_queens:
    def __init__(self, n):
        self.n = n
        self.state = [[0] * n for _ in range(n)]

    def _no_conflict(self, col):
        for i in range(self.n):
            if self.state[i][col] == 1:
                return False
        return True

    def action(self, row, col):
        if(self._no_conflict(col)):
            self.state[row][col] = 1
        return self.state

    def _remove_queen(self, row, col):
        if self.state[row][col] == 1:
            self.state[row][col] = 0
    
    def conflicts(self):
        queens = []
        for r in range(self.n):
            for c in range(self.n):
                if self.state[r][c] == 1:
                    queens.append((r, c))
        
        conflict_count = 0
        num_queens = len(queens)

        for i in range(num_queens):
            for j in range(i + 1, num_queens): 
                r1, c1 = queens[i]
                r2, c2 = queens[j]

                if c1 == c2 or abs(r1 - r2) == abs(c1 - c2) or r1 == r2:
                    conflict_count += 1
                    
        return conflict_count
    
    def queens_count(self):
        count = 0
        for row in self.state:
            count += sum(row)
        return count
    
    def is_solved(self):
        return self.queens_count() == self.n and self.conflicts() == 0
    
    def print_grid(self):
        for row in self.state:
            print(" ".join("Q" if col else "." for col in row))

    def possible_actions(self):
        actions = []
        for row in range(self.n):
            for col in range(self.n):
                if self.state[row][col] == 0 and self._no_conflict(col):
                    actions.append((row, col))
        return actions
    
    def load_state(self, state):
        if(len(state) == self.n and all(len(row) == self.n for row in state)):
            self.state = state
            return True
        return False