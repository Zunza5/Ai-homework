import queue
from n_queens import n_queens
import time

class A_star:
    def __init__(self, start, problem):
        self.start = tuple(tuple(row) for row in start)
        self.problem = problem
        self.frontier = queue.PriorityQueue()
        self.explored = set()
        self.came_from = {}
        self.g_scores_cache = {}
        self.heuristic_cache = {}
        self.node_expansions = 0
        self.average_branching_factor = 0
        self.max_branching_factor = 0
        self.min_branching_factor = float('inf')
        self.max_num_nodes_memory = 0
        self.time_taken = 0

    def heuristic(self, state):
        if(state in self.heuristic_cache):
            return self.heuristic_cache[state]

        placed_queens = []
        for r, row_data in enumerate(state):
            if 1 in row_data:
                c = row_data.index(1)
                placed_queens.append((r, c))
        
        n = len(state) 
        rows_populated = len(placed_queens)
        
        if rows_populated == n:
            return 0

        blocked_spots = 0
        
        for r in range(rows_populated, n):
            for c in range(n):
                is_attacked = False
                for (qr, qc) in placed_queens:
                    if c == qc or abs(r - qr) == abs(c - qc):
                        is_attacked = True
                        break
                if is_attacked:
                    blocked_spots += 1
                    
        return blocked_spots
    
    def f_scores(self, node):
        g_score = self.g_scores(node)
        h_score = self.heuristic(node)
        return g_score + h_score

    def reconstruct_path(self, current):
        total_path = [current]
        while current in self.came_from:
            current = self.came_from[current]
            total_path.append(current)
        return total_path[::-1]
    
    def g_scores(self, state):
        self.problem.load_state([list(row) for row in state])
        if(state in self.g_scores_cache):
            return self.g_scores_cache[state]
        g_score = self.came_from.get(state, None)
        if g_score is None:
            return 0
        return self.g_scores(g_score) + 1
    
    def a_star_search(self):
        start_time = time.time()
        self.frontier.put((self.f_scores(self.start), self.start))
        self.came_from = {}

        while not self.frontier.empty():
            current = self.frontier.get()[1]

            self.problem.load_state([list(row) for row in current])
            if(self.problem.is_solved()):
                self.average_branching_factor /= max(1, self.node_expansions)
                self.time_taken = time.time() - start_time
                return self.reconstruct_path(current)
            
            self.node_expansions += 1
            self.explored.add(current)

            self.problem.load_state([list(row) for row in current])
            actions = self.problem.possible_actions()
            
            branching_factor = len(actions)
            self.average_branching_factor += branching_factor
            self.max_branching_factor = max(self.max_branching_factor, branching_factor)
            self.min_branching_factor = min(self.min_branching_factor, branching_factor)

            for action in actions:

                row, col = action[0], action[1]
                self.problem.load_state([list(row) for row in current])
                new_state = self.problem.action(row, col)
                child = tuple(tuple(row) for row in new_state)
                self.came_from[child] = current
                tentative_g_score = self.g_scores(child)
                if child not in self.g_scores_cache or tentative_g_score < self.g_scores_cache[child]:
                    self.came_from[child] = current
                    self.g_scores_cache[child] = tentative_g_score
                    f = tentative_g_score + self.heuristic(child)
                    self.frontier.put((f, child))
        
            self.max_num_nodes_memory = max(self.max_num_nodes_memory, self.frontier.qsize() + len(self.explored))
                    
        return None 

    

queens = n_queens(4)
a_star_solver = A_star(queens.state, queens)
solution_path = a_star_solver.a_star_search()
if solution_path:
    for step in solution_path:
        queens.load_state([list(row) for row in step])
        queens.print_grid()
        print()
else:
    print("No solution found.")