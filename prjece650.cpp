#include <iostream>
#include <vector>
#include <sstream>
#include <minisat/core/Solver.h>
#include <numeric>
#include <algorithm>

using namespace std;

int vertices;
vector< pair<int,int> > edges;

bool cnf(Minisat::Solver& solver, int k) {
    for (int i = 0; i < vertices * k; i++)
        solver.newVar();

    // 1. At least one vertex is the ith vertex in the vertex cover
    for (int col = 0; col < k; col++) {
        Minisat::vec<Minisat::Lit> clause;
        for (int row = 0; row < vertices; row++)
            clause.push(Minisat::mkLit(row * k + col));
        solver.addClause(clause);
    }

    // 2. No one vertex can appear twice in a vertex cover
    for (int row = 0; row < vertices; row++)
        for (int col_q = 0; col_q < k; col_q++)
            for (int col_p = 0; col_p < col_q; col_p++)
                solver.addClause( ~Minisat::mkLit(row * k + col_p), ~Minisat::mkLit(row * k + col_q));

    // 3. No more than one vertex in the ith position of the vertex cover
    for (int col = 0; col < k; col++)
        for (int row_q = 0; row_q < vertices; row_q++)
            for (int row_p = 0; row_p < row_q; row_p++)
                solver.addClause( ~Minisat::mkLit(row_p * k + col), ~Minisat::mkLit(row_q * k + col));

    // 4. Every edge is incident to at least one vertex
    for ( pair<int, int> edge : edges) {
        Minisat::vec<Minisat::Lit> clause;
        for (int col = 0; col < k; col++) {
            int row_i = edge.first;
            int row_j = edge.second;
            clause.push(Minisat::mkLit(row_i * k + col));
            clause.push(Minisat::mkLit(row_j * k + col));
        }
        solver.addClause(clause);
    }

    return solver.solve();
}

bool cnf_3(Minisat::Solver& solver, int k) {
    for (int i = 0; i < 1000; i++)
        solver.newVar();
    int b = vertices * k;

    // 1. At least one vertex is the ith vertex in the vertex cover
    for (int col = 0; col < k; col++) {
        Minisat::vec<Minisat::Lit> clause;
        for (int row = 0; row < vertices; row++)
            clause.push(Minisat::mkLit(row * k + col));

        //CNF to 3-CNF
        int size = clause.size();
        solver.addClause(clause[0], Minisat::mkLit(b));
        for(int i=1; i<size-1; i++){
            b++;
            solver.addClause(~Minisat::mkLit(b-1), clause[i], Minisat::mkLit(b));
        }
        solver.addClause(~Minisat::mkLit(b), clause[size-1]);
        b++;
    }

    // 2. No one vertex can appear twice in a vertex cover
    for (int row = 0; row < vertices; row++)
        for (int col_q = 0; col_q < k; col_q++)
            for (int col_p = 0; col_p < col_q; col_p++)
                solver.addClause( ~Minisat::mkLit(row * k + col_p), ~Minisat::mkLit(row * k + col_q));

    // 3. No more than one vertex in the ith position of the vertex cover
    for (int col = 0; col < k; col++)
        for (int row_q = 0; row_q < vertices; row_q++)
            for (int row_p = 0; row_p < row_q; row_p++)
                solver.addClause( ~Minisat::mkLit(row_p * k + col), ~Minisat::mkLit(row_q * k + col));

    // 4. Every edge is incident to at least one vertex
    for ( pair<int, int> edge : edges) {
        Minisat::vec<Minisat::Lit> clause;
        for (int col = 0; col < k; col++) {
            int row_i = edge.first;
            int row_j = edge.second;
            clause.push(Minisat::mkLit(row_i * k + col));
            clause.push(Minisat::mkLit(row_j * k + col));
        }

        int size = clause.size();
        if (size <= 3)
            solver.addClause(clause);
        else{
            //CNF to 3-CNF
            solver.addClause(clause[0], Minisat::mkLit(b));
            for(int i=1; i<size-1; i++){
                b++;
                solver.addClause(~Minisat::mkLit(b-1), clause[i], Minisat::mkLit(b));
            }
            solver.addClause(~Minisat::mkLit(b), clause[size-1]);
            b++;
        }
    }

    return solver.solve();
}

vector<int> get_vertex_cover(Minisat::Solver& solver, int k) {
    vector<int> vertex_cover;
    for (int row = 0; row < vertices; row++)
        for (int col = 0; col < k; col++)
            if (solver.modelValue(row * k + col) == Minisat::l_True)
                vertex_cover.push_back(row);
    return vertex_cover;
}

void minimal(int approach) {
    int vertex_result[vertices];
    vector<int> minimal_vertex_cover;
    for(int i = 0; i< vertices; i++)
        vertex_result[i] = -1;

    // print CNF-SAT-VC
    if (approach == 0){
        for (int i = 0; i <= vertices; i++) {
            Minisat::Solver solver;
            vertex_result[i] = cnf(solver, i);
            if (vertex_result[i]) {
                minimal_vertex_cover = get_vertex_cover(solver, i);
                size_t vertex_num = minimal_vertex_cover.size();
                cout << "CNF-SAT-VC: ";
                for (int j = 0; j< vertex_num - 1; j++)
                    cout << minimal_vertex_cover[j] << " ";
                cout << minimal_vertex_cover[vertex_num - 1] << endl;
                return;
            }
        }
    }

    // print CNF-3-SAT-VC
    if (approach == 1){
        for (int i = 0; i <= vertices; i++) {
            Minisat::Solver solver;
            vertex_result[i] = cnf_3(solver, i);
            if (vertex_result[i]) {
                minimal_vertex_cover = get_vertex_cover(solver, i);
                size_t vertex_num = minimal_vertex_cover.size();
                cout << "CNF-3-SAT-VC: ";
                for (int j = 0; j< vertex_num - 1; j++)
                    cout << minimal_vertex_cover[j] << " ";
                cout << minimal_vertex_cover[vertex_num - 1] << endl;
                return;
            }
        }
    }
}

void get_edges(string coordinate) {
    edges.clear();
    string x,y;
    for (int i=0;i<coordinate.size();i++){
        if (coordinate[i] == '<'){
            x.push_back(coordinate[i+1]);
            if (coordinate[i+2] != ','){
                x.push_back(coordinate[i+2]);
                if (coordinate[i+3] != ',')
                    x.push_back(coordinate[i+3]);
            }
            x.push_back(' ');
        }

        if (coordinate[i] == ',' && coordinate[i+1] != '<'){
            y.push_back(coordinate[i+1]);
            if (coordinate[i+2] != '>'){
                y.push_back(coordinate[i+2]);
                if (coordinate[i+3] != '>')
                    y.push_back(coordinate[i+3]);
            }
            y.push_back(' ');
        }
    }

    stringstream x_value(x);
    stringstream y_value(y);
    int x_int;
    int y_int;
    while(x_value >> x_int && y_value >> y_int) {
        pair<int, int> edge;
        edge.first = x_int;
        edge.second = y_int;
        edges.push_back(edge);
    }

}

std::vector<int> approxvc2(int V, std::vector<std::pair<int, int>> edges)
{
    std::vector<int> res;
    std::vector<std::vector<bool>> matrix(V, std::vector<bool>(V, 0));
    std::vector<int> range(V);
    std::iota(range.begin(), range.end(), 0);
    for (short int i = 0; i < edges.size(); i++)
    {
        int j = edges[i].first;
        int k = edges[i].second;
        matrix[j][k] = true;
        matrix[k][j] = true;
    }
    //     for (const auto& inner_vec : matrix) {
    //     for (const auto& val : inner_vec) {
    //         std::cout << val << " ";
    //     }
    //     std::cout << std::endl;
    // }
    for (short int i : range)
    {
        for (short int j : range)
        {
            if (matrix[i][j] == true)
            {
                res.push_back(i);
                res.push_back(j);
                matrix[i][j] = false;
                matrix[j][i] = false;
                int iter = 0;
                while (iter < V)
                {
                    matrix[i][iter] = false;
                    matrix[j][iter] = false;
                    matrix[iter][i] = false;
                    matrix[iter][j] = false;
                    iter++;
                }
                // for (int i = 0; i < matrix.size(); i++) {
                //         for (int j = 0; j < matrix[i].size(); j++) {
                //             std::cout << matrix[i][j] << " ";

                //         }
                //         std::cout << std::endl;
                //     }
                // std::cout << std::endl;
            }
        }
    }
    std::sort(res.begin(), res.end());

    return res;
}

int main() {
    string input;
    string initial;

    while (true) {
        getline(cin, input);
        if (cin.eof())
            break;

        istringstream split(input);
        split >> initial;

        if (initial == "V") {
            split >> vertices;
        }

        if (initial == "E") {
            string coordinate;
            string c;
            while (split >> c)
                coordinate += c;
            if (coordinate == "{}")
                cout << "";
            else {
                get_edges(coordinate);
                minimal(0); // print CNF-SAT-VC
                minimal(1); // print CNF-3-SAT-VC
            }
        }
    }
}