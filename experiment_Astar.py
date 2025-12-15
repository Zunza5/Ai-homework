from n_queens import n_queens
from A_star import A_star
import matplotlib.pyplot as plt
from concurrent.futures import ProcessPoolExecutor
import multiprocessing

def run_experiment(n):
    """Run A* on n-Queens and return metrics"""
    queens = n_queens(n)
    a_star_solver = A_star(queens.state, queens)
    path = a_star_solver.a_star_search()
    
    if path is not None:
        return {
            'n': n,
            'time': a_star_solver.time_taken,
            'node_expansions': a_star_solver.node_expansions,
            'max_memory': a_star_solver.max_num_nodes_memory,
            'avg_branching': a_star_solver.average_branching_factor,
            'max_branching': a_star_solver.max_branching_factor,
            'min_branching': a_star_solver.min_branching_factor,
            'solved': True
        }
    else:
        return {
            'n': n,
            'solved': False
        }

if __name__ == '__main__':
    # Run experiments sequentially
    n_values = range(4, 8)  # You can adjust the range as needed
    results = []
    
    for n in n_values:
        print(f"Running experiment for n={n}...")
        result = run_experiment(n)
        results.append(result)
        if result['solved']:
            print(f"  Completed in {result['time']:.4f}s")
        else:
            print(f"  Failed to solve")
        print()
    
    # Filter solved results
    solved_results = [r for r in results if r['solved']]
    
    # Print results
    for r in solved_results:
        print(f"Solved {r['n']}-Queens with A* in {r['time']:.4f} seconds")
        print(f"Node Expansions: {r['node_expansions']}")
        print(f"Max Nodes in Memory: {r['max_memory']}")
        print(f"Average Branching Factor: {r['avg_branching']:.2f}")
        print(f"Max Branching Factor: {r['max_branching']}")
        print(f"Min Branching Factor: {r['min_branching']}")
        print()
    
    # Create plots
    if solved_results:
        fig, axes = plt.subplots(2, 2, figsize=(12, 10))
        fig.suptitle('A* Algorithm Performance on N-Queens Problem', fontsize=16)
        
        n_vals = [r['n'] for r in solved_results]
        times = [r['time'] for r in solved_results]
        expansions = [r['node_expansions'] for r in solved_results]
        memory = [r['max_memory'] for r in solved_results]
        avg_branch = [r['avg_branching'] for r in solved_results]
        
        # Time plot
        axes[0, 0].plot(n_vals, times, marker='o', color='blue', linewidth=2)
        axes[0, 0].set_xlabel('N (Board Size)')
        axes[0, 0].set_ylabel('Time (seconds)')
        axes[0, 0].set_title('Execution Time vs N')
        axes[0, 0].grid(True, alpha=0.3)
        
        # Node expansions plot
        axes[0, 1].plot(n_vals, expansions, marker='s', color='green', linewidth=2)
        axes[0, 1].set_xlabel('N (Board Size)')
        axes[0, 1].set_ylabel('Node Expansions')
        axes[0, 1].set_title('Node Expansions vs N')
        axes[0, 1].grid(True, alpha=0.3)
        
        # Memory usage plot
        axes[1, 0].plot(n_vals, memory, marker='^', color='red', linewidth=2)
        axes[1, 0].set_xlabel('N (Board Size)')
        axes[1, 0].set_ylabel('Max Nodes in Memory')
        axes[1, 0].set_title('Memory Usage vs N')
        axes[1, 0].grid(True, alpha=0.3)
        
        # Branching factor plot
        axes[1, 1].plot(n_vals, avg_branch, marker='d', color='purple', linewidth=2)
        axes[1, 1].set_xlabel('N (Board Size)')
        axes[1, 1].set_ylabel('Average Branching Factor')
        axes[1, 1].set_title('Avg Branching Factor vs N')
        axes[1, 1].grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.savefig('a_star_experiments.png', dpi=300, bbox_inches='tight')
        print("Plot saved as 'a_star_experiments.png'")
        plt.show()
    else:
        print("No experiments were successfully solved.")