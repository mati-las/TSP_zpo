#include "TSP.hxx"
#include "tsp_setup.hxx"
#include <algorithm>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <numeric>

std::ostream& operator<<(std::ostream& os, const CostMatrix& cm) {
    for (std::size_t r = 0; r < cm.size(); ++r) {
        for (std::size_t c = 0; c < cm.size(); ++c) {
            const auto& elem = cm[r][c];
            os << (is_inf(elem) ? "INF" : std::to_string(elem)) << " ";
        }
        os << "\n";
    }
    return os;
}

/* PART 1 */
path_t StageState::get_path() {
    std::vector<vertex_t> edges = unsorted_path_;

    for (std::size_t r = 0; r < matrix_.size(); ++r) {
        for (std::size_t c = 0; c < matrix_.size(); ++c) {
            if (matrix_[r][c] != INF) {
                edges.push_back({r, c});
            }
        }
    }

    std::vector<std::size_t> next_vertex(matrix_.size());
    for (const auto& edge : edges) {
        next_vertex[edge.row] = edge.col;
    }

    path_t sorted_path;
    if (edges.empty()) return sorted_path;

    std::size_t current = 0;
    for (std::size_t i = 0; i < matrix_.size(); ++i) {
        sorted_path.push_back(current);
        current = next_vertex[current];
    }

    return sorted_path;
}

/* Minimalne wartości w wierszach */
std::vector<cost_t> CostMatrix::get_min_values_in_rows() const {
    std::vector<cost_t> row_mins;
    row_mins.reserve(matrix_.size());

    for (const auto& row : matrix_) {
        if (row.empty()) {
            row_mins.push_back(0);
            continue;
        }
        auto min_it = std::min_element(row.begin(), row.end());
        cost_t min_val = *min_it;
        if (min_val == INF) min_val = 0;
        row_mins.push_back(min_val);
    }

    return row_mins;
}

/* Redukcja wierszy */
cost_t CostMatrix::reduce_rows() {
    cost_t reduction_sum = 0;
    auto row_mins = get_min_values_in_rows();

    for (std::size_t r = 0; r < row_mins.size(); ++r) {
        if (row_mins[r] == 0 || row_mins[r] == INF) continue;
        reduction_sum += row_mins[r];
        for (auto& val : matrix_[r]) {
            if (val != INF) val -= row_mins[r];
        }
    }
    return reduction_sum;
}

/* Minimalne wartości w kolumnach */
std::vector<cost_t> CostMatrix::get_min_values_in_cols() const {
    std::vector<cost_t> col_mins;

    if (matrix_.empty() || matrix_[0].empty()) return {};

    std::size_t n_rows = matrix_.size();
    std::size_t n_cols = matrix_[0].size();
    col_mins.reserve(n_cols);

    for (std::size_t col = 0; col < n_cols; ++col) {
        cost_t min_val = matrix_[0][col];
        for (std::size_t row = 1; row < n_rows; ++row) {
            if (matrix_[row][col] < min_val) min_val = matrix_[row][col];
        }
        if (min_val == INF) min_val = 0;
        col_mins.push_back(min_val);
    }

    return col_mins;
}

/* Redukcja kolumn */
cost_t CostMatrix::reduce_cols() {
    cost_t reduction_sum = 0;
    auto col_mins = get_min_values_in_cols();

    for (std::size_t col = 0; col < col_mins.size(); ++col) {
        if (col_mins[col] == 0 || col_mins[col] == INF) continue;
        reduction_sum += col_mins[col];
        for (std::size_t row = 0; row < matrix_.size(); ++row) {
            if (matrix_[row][col] != INF) matrix_[row][col] -= col_mins[col];
        }
    }

    return reduction_sum;
}

/* Koszt nieodwiedzenia wierzchołka */
cost_t CostMatrix::get_vertex_cost(std::size_t row, std::size_t col) const {
    cost_t min_row = INF;
    cost_t min_col = INF;

    for (std::size_t r = 0; r < matrix_.size(); ++r) {
        if (r != row && matrix_[r][col] != INF && matrix_[r][col] < min_col) min_col = matrix_[r][col];
    }
    for (std::size_t c = 0; c < matrix_.size(); ++c) {
        if (c != col && matrix_[row][c] != INF && matrix_[row][c] < min_row) min_row = matrix_[row][c];
    }

    if (min_row == INF) min_row = 0;
    if (min_col == INF) min_col = 0;

    return min_row + min_col;
}

/* ----------------------- PART 2: Algorytm TSP ----------------------- */

/* Wybór kolejnego wierzchołka */
NewVertex StageState::choose_new_vertex() {
    vertex_t selected_vertex{0, 0};
    cost_t max_cost = -1;

    for (std::size_t r = 0; r < matrix_.size(); ++r) {
        for (std::size_t c = 0; c < matrix_.size(); ++c) {
            if (matrix_[r][c] == 0) {
                cost_t vertex_cost = matrix_.get_vertex_cost(r, c);
                if (vertex_cost > max_cost) {
                    max_cost = vertex_cost;
                    selected_vertex = {r, c};
                }
            }
        }
    }

    return NewVertex(selected_vertex, max_cost);
}

/* Aktualizacja macierzy kosztów po wybraniu wierzchołka */
void StageState::update_cost_matrix(vertex_t chosen) {
    for (std::size_t r = 0; r < matrix_.size(); ++r) matrix_[r][chosen.col] = INF;
    for (std::size_t c = 0; c < matrix_.size(); ++c) matrix_[chosen.row][c] = INF;
    matrix_[chosen.col][chosen.row] = INF;
}

/* Redukcja macierzy kosztów */
cost_t StageState::reduce_cost_matrix() {
    return matrix_.reduce_rows() + matrix_.reduce_cols();
}

/* Koszt całkowity dla optymalnej ścieżki */
cost_t get_optimal_cost(const path_t& path, const cost_matrix_t& matrix) {
    cost_t total_cost = 0;
    for (std::size_t i = 1; i < path.size(); ++i) total_cost += matrix[path[i-1]][path[i]];
    total_cost += matrix[path.back()][path[0]];
    return total_cost;
}

/* Utworzenie gałęzi prawej (z zabronionym wierzchołkiem) */
StageState create_right_branch_matrix(CostMatrix matrix, vertex_t vertex, cost_t lb, unsorted_path_t path) {
    matrix[vertex.row][vertex.col] = INF;
    return StageState(matrix, path, lb);
}

/* Zachowanie tylko optymalnych rozwiązań */
tsp_solutions_t filter_solutions(tsp_solutions_t solutions) {
    cost_t best_cost = INF;
    for (const auto& sol : solutions) best_cost = std::min(best_cost, sol.lower_bound);

    tsp_solutions_t filtered;
    std::copy_if(solutions.begin(), solutions.end(), std::back_inserter(filtered),
                 [best_cost](const tsp_solution_t& sol) { return sol.lower_bound == best_cost; });
    return filtered;
}

/* Rozwiązanie problemu TSP */
tsp_solutions_t solve_tsp(const cost_matrix_t& cm) {
    StageState branch(cm);
    std::stack<StageState> stack;
    stack.push(branch);

    cost_t best_lb = INF;
    tsp_solutions_t solutions;
    std::size_t final_level = cm.size() - 2;

    while (!stack.empty()) {
        branch = stack.top();
        stack.pop();

        while (branch.get_level() != final_level && branch.get_lower_bound() <= best_lb) {
            if (branch.get_level() == 0) branch.reset_lower_bound();

            cost_t reduction_cost = branch.reduce_cost_matrix();
            branch.update_lower_bound(reduction_cost);
            if (branch.get_lower_bound() > best_lb) break;

            NewVertex next_vertex = branch.choose_new_vertex();

            CostMatrix prev_matrix = branch.get_matrix();
            unsorted_path_t prev_path = branch.get_unsorted_path();
            branch.append_to_path(next_vertex.coordinates);
            branch.update_cost_matrix(next_vertex.coordinates);

            cost_t right_branch_lb = (branch.get_lower_bound() == INF || next_vertex.cost == INF)
                                     ? INF
                                     : branch.get_lower_bound() + next_vertex.cost;

            stack.push(create_right_branch_matrix(prev_matrix, next_vertex.coordinates, right_branch_lb, prev_path));
        }

        if (branch.get_lower_bound() <= best_lb) {
            best_lb = branch.get_lower_bound();
            path_t complete_path = branch.get_path();
            solutions.push_back({get_optimal_cost(complete_path, cm), complete_path});
        }
    }

    return filter_solutions(solutions);
}