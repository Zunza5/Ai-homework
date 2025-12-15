# Ai-Homework: N-Queens Solvers & Performance Analysis
This repository contains implementations of different Artificial Intelligence approaches to solve the classic **N-Queens Problem**. The project explores both search algorithms (A*) and Constraint Satisfaction Problems (CSP) using modern libraries, complete with scripts to benchmark and visualize performance.

## Project Overview
The project is structured around a base class that defines the game rules and includes two distinct solvers:

1. **CSP (Constraint Satisfaction Problem):** Utilizes the **Z3 SMT solver** to efficiently find valid solutions by satisfying spatial constraints.
2. **A Search:** Implements the A* search algorithm with a custom heuristic function to navigate the state space.

In addition to the solvers, the repository includes **experiment scripts** that analyze metrics such as execution time, branching factors, and memory usage across different board sizes (N).

## Requirements
The project is managed via **PDM** and requires:

* Python **3.11**
* **z3-solver** (>=4.15.4.0)
* **matplotlib** (>=3.10.8) for generating performance plots.

## Installation
Ensure you have [PDM](https://pdm.fming.dev/) installed on your system.

1. Clone the repository.
2. Install dependencies:

```bash
pdm install

```

## Usage
You can run the solvers or the experiment suites directly via Python (or `pdm run`).

### 1. Run Individual Solvers**CSP Solver (Z3)**
Solves a single instance (default N=20).

```bash
pdm run python csp.py

```

**A Solver**
Solves a single instance (default N=4) and prints the steps.

```bash
pdm run python A_star.py

```

### 2. Run Performance Experiments
**CSP Experiments**
Runs the Z3 solver for N=4 to 19, collecting metrics like time, constraints, and propagations.

```bash
pdm run python experiment_csp.py

```

* **Output:** Generates `csp_z3_experiments.png` containing 5 plots (Execution Time, Constraints vs N, Propagations, etc.).

**A Experiments**
Runs the A* algorithm for N=4 to 7. It tracks time, node expansions, memory usage, and branching factors.

```bash
pdm run python experiment_Astar.py

```

* **Output:** Generates `a_star_experiments.png` containing 4 plots (Time, Node Expansions, Memory Usage, Branching Factor).

## File Structure
**`n_queens.py`**: Base class defining the board, placement rules, and conflict detection.
* **`csp.py`**: CSP solver implementation using `z3-solver`. Maps constraints to integer variables.
* **`A_star.py`**: A* algorithm implementation with `PriorityQueue` and a custom heuristic function.
* **`experiment_csp.py`**: Benchmarking script for the CSP solver. Generates performance graphs using Matplotlib.
* **`experiment_Astar.py`**: Benchmarking script for the A* solver.
* **`pyproject.toml`**: Project configuration and dependency management.

## Results
The experiments generate visual insights into the algorithms' behavior:

* **A Search:** Shows exponential growth in time and memory as N increases, highlighting the impact of the branching factor.
* **CSP (Z3):** Demonstrates high efficiency for larger N, tracking metrics like constraint propagations and decisions.

## Author **Zualdi Luca** 
