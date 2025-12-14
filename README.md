# Ai-Homework: N-Queens Problem Solvers
This repository contains implementations of different Artificial Intelligence approaches to solve the classic **N-Queens Problem**. The project explores both search algorithms (A*) and Constraint Satisfaction Problems (CSP) using modern libraries.

##  Project DescriptionThe project is structured around a base class that defines the game rules, including two distinct solvers:

1. **CSP (Constraint Satisfaction Problem):** Uses the **Z3** SMT solver to find a valid solution by satisfying the spatial constraints of the queens.
2. **A* Search:** Implements the A* search algorithm with a custom heuristic function to navigate the state space.

##  Requirements
The project is managed via **PDM** and requires:

* Python **3.11**
* **z3-solver** (>=4.15.4.0)

##  Installation
Ensure you have [PDM](https://pdm.fming.dev/) installed on your system.

1. Clone the repository.
2. Install dependencies:

```bash
pdm install

```

## Usage
You can run the different solvers directly via Python (or via `pdm run`).

### Run the CSP Solver (Z3)
This script solves the problem for **N=20** (default) using the Z3 solver.

```bash
pdm run python csp.py

```

*Output:* Prints the solved grid or a message if no solution is found.

### Run the A* Solver
This script solves the problem for **N=8** (default), showing the algorithm's steps.

```bash
pdm run python A_star.py

```

*Output:* Prints the sequence of states from the initial configuration to the final solution.

## 📂 File StructureHere is an overview of the main files in the repository:

* **`n_queens.py`**: Defines the `n_queens` class. Handles the board, placement rules, conflict checking, and grid visualization. It is the base used by the other scripts.
* **`csp.py`**: Implementation of the CSP solver. Maps the problem to Z3 integer variables and enforces constraints on rows, columns, and diagonals.
* **`A_star.py`**: Implementation of the A* algorithm. Includes `PriorityQueue` management, path reconstruction, and a heuristic function that estimates "blocked spots" (attacked positions).
* **`pyproject.toml` / `pdm.lock`**: Configuration files for dependency and package management.

##  Author **Zualdi Luca**
