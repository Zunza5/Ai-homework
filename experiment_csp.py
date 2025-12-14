from n_queens import n_queens
from csp import z3_solver
import matplotlib.pyplot as plt
import time
import z3

def run_csp_experiment(n):
    """Run CSP (Z3) solver on n-Queens and return metrics"""
    queens = n_queens(n)
    csp_solver = z3_solver(queens)
    
    # Time the solve operation
    start_time = time.time()
    solution_check = csp_solver.s.check()
    csp_solver.time_taken = time.time() - start_time
    
    # Get solver statistics
    statistics = csp_solver.s.statistics()
    
    if str(solution_check) == 'sat':
        model = csp_solver.s.model()
        
        # Extract relevant statistics
        stats_dict = {
            'num_constraints': len(csp_solver.s.assertions()),
            'num_variables': len(csp_solver.vars),
            'decisions': 0,
            'propagations': 0,
            'conflicts': 0,
            'mk_bool_var': 0,
            'case_split': 0,
        }
        
        # Safely extract statistics from Z3
        for key in stats_dict.keys():
            try:
                val = statistics.get(key) if hasattr(statistics, 'get') else getattr(statistics, key, 0)
                if val is not None:
                    stats_dict[key] = int(val) if key != 'memory' else val
            except:
                stats_dict[key] = 0
        
        return {
            'n': n,
            'time': csp_solver.time_taken,
            'solved': True,
            'num_constraints': stats_dict['num_constraints'],
            'num_variables': stats_dict['num_variables'],
            'decisions': stats_dict['decisions'],
            'propagations': stats_dict['propagations'],
            'conflicts': stats_dict['conflicts'],
            'mk_bool_var': stats_dict['mk_bool_var'],
            'case_split': stats_dict['case_split'],
        }
    else:
        return {
            'n': n,
            'solved': False
        }

if __name__ == '__main__':
    # Run experiments sequentially
    n_values = range(4, 20)
    csp_results = []
    
    print("="*60)
    print("Running CSP (Z3) experiments...")
    print("="*60)
    for n in n_values:
        print(f"Running CSP for n={n}...")
        result = run_csp_experiment(n)
        csp_results.append(result)
        if result['solved']:
            print(f"  Time: {result['time']:.4f}s")
            print(f"  Constraints: {result['num_constraints']}")
            print(f"  Variables: {result['num_variables']}")
            if result.get('decisions') > 0:
                print(f"  Decisions: {result['decisions']}")
            if result.get('propagations') > 0:
                print(f"  Propagations: {result['propagations']}")
        else:
            print(f"  Failed to solve")
        print()
    
    # Filter solved results
    solved_csp = [r for r in csp_results if r['solved']]
    
    # Print detailed results
    print("\n" + "="*100)
    print("CSP (Z3) Results Summary")
    print("="*100)
    print(f"{'N':>3} | {'Time (s)':>10} | {'Constraints':>12} | {'Variables':>9} | {'Decisions':>9} | {'Propagations':>12} | {'Conflicts':>9}")
    print("-" * 100)
    for r in solved_csp:
        print(f"{r['n']:>3} | {r['time']:>10.4f} | {r['num_constraints']:>12} | {r['num_variables']:>9} | {r['decisions']:>9} | {r['propagations']:>12} | {r['conflicts']:>9}")
    
    # Create plots
    if solved_csp:
        fig, axes = plt.subplots(3, 3, figsize=(18, 14))
        fig.suptitle('CSP (Z3) Solver Performance Analysis on N-Queens Problem', fontsize=16, fontweight='bold')
        
        csp_n = [r['n'] for r in solved_csp]
        csp_times = [r['time'] for r in solved_csp]
        csp_constraints = [r['num_constraints'] for r in solved_csp]
        csp_variables = [r['num_variables'] for r in solved_csp]
        csp_decisions = [r['decisions'] for r in solved_csp]
        csp_propagations = [r['propagations'] for r in solved_csp]
        csp_conflicts = [r['conflicts'] for r in solved_csp]
        csp_mk_bool = [r['mk_bool_var'] for r in solved_csp]
        csp_case_split = [r['case_split'] for r in solved_csp]
        
        # 1. Time plot
        axes[0, 0].plot(csp_n, csp_times, marker='s', linewidth=2.5, color='red', markersize=8)
        axes[0, 0].set_xlabel('N (Board Size)', fontsize=11)
        axes[0, 0].set_ylabel('Time (seconds)', fontsize=11)
        axes[0, 0].set_title('Execution Time vs N')
        axes[0, 0].grid(True, alpha=0.3)
        
        # 2. Constraints plot
        axes[0, 1].plot(csp_n, csp_constraints, marker='o', linewidth=2.5, color='blue', markersize=8)
        axes[0, 1].set_xlabel('N (Board Size)', fontsize=11)
        axes[0, 1].set_ylabel('Number of Constraints', fontsize=11)
        axes[0, 1].set_title('Constraints vs N')
        axes[0, 1].grid(True, alpha=0.3)
        
        # 3. Variables plot
        axes[0, 2].plot(csp_n, csp_variables, marker='^', linewidth=2.5, color='green', markersize=8)
        axes[0, 2].set_xlabel('N (Board Size)', fontsize=11)
        axes[0, 2].set_ylabel('Number of Variables', fontsize=11)
        axes[0, 2].set_title('Variables vs N')
        axes[0, 2].grid(True, alpha=0.3)
        
        # 4. Decisions plot
        axes[1, 0].plot(csp_n, csp_decisions, marker='d', linewidth=2.5, color='orange', markersize=8)
        axes[1, 0].set_xlabel('N (Board Size)', fontsize=11)
        axes[1, 0].set_ylabel('Number of Decisions', fontsize=11)
        axes[1, 0].set_title('Solver Decisions vs N')
        axes[1, 0].grid(True, alpha=0.3)
        
        # 5. Propagations plot
        axes[1, 1].plot(csp_n, csp_propagations, marker='*', linewidth=2.5, color='purple', markersize=12)
        axes[1, 1].set_xlabel('N (Board Size)', fontsize=11)
        axes[1, 1].set_ylabel('Number of Propagations', fontsize=11)
        axes[1, 1].set_title('Constraint Propagations vs N')
        axes[1, 1].grid(True, alpha=0.3)
        
        # 6. Conflicts plot
        axes[1, 2].plot(csp_n, csp_conflicts, marker='v', linewidth=2.5, color='brown', markersize=8)
        axes[1, 2].set_xlabel('N (Board Size)', fontsize=11)
        axes[1, 2].set_ylabel('Number of Conflicts', fontsize=11)
        axes[1, 2].set_title('Conflicts Detected vs N')
        axes[1, 2].grid(True, alpha=0.3)
        
        # 7. Time per constraint (efficiency)
        time_per_constraint = [r['time'] / r['num_constraints'] if r['num_constraints'] > 0 else 0 
                               for r in solved_csp]
        axes[2, 0].plot(csp_n, time_per_constraint, marker='p', linewidth=2.5, color='cyan', markersize=8)
        axes[2, 0].set_xlabel('N (Board Size)', fontsize=11)
        axes[2, 0].set_ylabel('Time per Constraint (ms)', fontsize=11)
        axes[2, 0].set_title('Efficiency: Time/Constraint')
        axes[2, 0].grid(True, alpha=0.3)
        
        # 8. Boolean variables created
        axes[2, 1].plot(csp_n, csp_mk_bool, marker='x', linewidth=2.5, color='magenta', markersize=8)
        axes[2, 1].set_xlabel('N (Board Size)', fontsize=11)
        axes[2, 1].set_ylabel('Boolean Variables Created', fontsize=11)
        axes[2, 1].set_title('Boolean Variables vs N')
        axes[2, 1].grid(True, alpha=0.3)
        
        # 9. Case splits (branching)
        axes[2, 2].plot(csp_n, csp_case_split, marker='H', linewidth=2.5, color='teal', markersize=8)
        axes[2, 2].set_xlabel('N (Board Size)', fontsize=11)
        axes[2, 2].set_ylabel('Case Splits', fontsize=11)
        axes[2, 2].set_title('Case Splits (Branching) vs N')
        axes[2, 2].grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.savefig('csp_z3_experiments.png', dpi=300, bbox_inches='tight')
        print("\nPlot saved as 'csp_z3_experiments.png'")
        plt.show()
    else:
        print("\nNo experiments were successfully solved.")