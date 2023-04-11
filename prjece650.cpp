#include <iostream>
#include <vector>
#include <sstream>
#include <minisat/core/Solver.h>
#include <numeric>
#include <algorithm>
#include <set>
#include <pthread.h>
#include <ctime>

using namespace std;

int vertices;
vector< pair<int,int> > edges;
pthread_t io_thread, cnf_thread, cnf_3_thread, vc_1_thread, refined_vc_1_thread, vc_2_thread, refined_vc_2_thread;
vector<int> cnf_result, cnf_3_result, vc2_result, refined_vc2_result;
set<int> vc1_result, refined_vc1_result;
bool cnf_thread_status, cnf_thread_timeout = false;
bool cnf_3_thread_status, cnf_3_thread_timeout = false;

vector<vector<int>> get_adj(int v, vector< pair<int,int> > e){
    vector<vector<int>> adj(v);

    for(int i=0;i<v;i++)
        adj[i].resize(v);

    for(auto& j: e){
        adj[j.first][j.second] = 1;
        adj[j.second][j.first] = 1;
    }
    return adj;
}

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

set<int> approxvc1(){
    vector<vector<int>> adj(vertices);
    set<int> cover_set;
    adj = get_adj(vertices, edges);
    while(true){
        int max_degree = 0;
        int max_vertex = -1;
        for(int i=0; i<vertices; i++){
            int degree = 0;
            for(int j=0; j<vertices; j++)
                if(adj[i][j] == 1)
                    degree++;
            if(degree > max_degree){
                max_vertex = i;
                max_degree = degree;
            }
        }
        if(max_vertex == -1)
            break;
        cover_set.insert(max_vertex);
        for(int k=0; k<vertices; k++){
            adj[max_vertex][k] = 0;
            adj[k][max_vertex] = 0;
        }
    }
    return cover_set;
}

set<int> refined_approxvc1(){
    vector<vector<int>> adj(vertices);
    adj = get_adj(vertices, edges);
    set<int> cover_set = approxvc1();
    set<int> unnecessary;
    set<int> temp_cover = cover_set;
    for (int vertex : temp_cover) {
        cover_set.erase(vertex);

        bool isCover = true;
        for (int i=0; i<vertices; i++) {
            if(adj[vertex][i] == 1)
                if (cover_set.find(i) == cover_set.end()) {
                    isCover = false;
                    break;
                }
        }
        if (!isCover) {
            cover_set.insert(vertex);
        } else {
            unnecessary.insert(vertex);
        }
    }

    for (int vertex : unnecessary) {
        cover_set.erase(vertex);
    }
    return cover_set;
}

vector<int> approxvc2()
{
    vector<int> res;
    vector<int> range(vertices);
    iota(range.begin(), range.end(), 0);
    vector<vector<int>> matrix(vertices);
    matrix = get_adj(vertices, edges);
    for (short int i : range)
    {
        for (short int j : range)
        {
            if (matrix[i][j] == 1)
            {
                res.push_back(i);
                res.push_back(j);
                matrix[i][j] = 0;
                matrix[j][i] = 0;
                int iter = 0;
                while (iter < vertices)
                {
                    matrix[i][iter] = 0;
                    matrix[j][iter] = 0;
                    matrix[iter][i] = 0;
                    matrix[iter][j] = 0;
                    iter++;
                }
            }
        }
    }
    sort(res.begin(), res.end());

    return res;
}

bool checkMinVertCov(int V, vector<int> arr, vector<vector<int>> matrix)      // PaRT OF REFAPPROXVC2
{
    vector<vector<int>> tempMatrix = matrix;
    for (int i = 0; i < V; i++)
    {
        for (int j = 0; j < V; j++)
        {
            if (tempMatrix[i][j] == 1 && find(arr.begin(), arr.end(), i) == arr.end() &&
                find(arr.begin(), arr.end(), j) == arr.end())
            {
                tempMatrix[i][j] = 0;
            }
        }
    }
    if (tempMatrix.size() != matrix.size())
    {
        return false;
    }
    for (size_t i = 0; i < tempMatrix.size(); ++i)
    {
        if (tempMatrix[i] != matrix[i])
        {
            return false;
        }
    }
    return true;
}

vector<int> refined_approxvc2()
{
    vector<int> arr = approxvc2();
    vector<vector<int>> matrix(vertices);
    matrix = get_adj(vertices, edges);
    int iter = 0;
    int size = arr.size();
    for (int i = 0; i < size; i++)
    {
        int flag = 0;
        int temp;
        temp = arr.at(iter);
        arr.erase(arr.begin() + iter);

        if (checkMinVertCov(vertices, arr, matrix))
        {
            flag++;
        }
        if (flag == 0)
        {
            arr.insert(arr.begin() + iter, temp);
            iter++;
        }
    }
    return arr;
}

vector<int> get_vertex_cover(Minisat::Solver& solver, int k) {
    vector<int> vertex_cover;
    for (int row = 0; row < vertices; row++)
        for (int col = 0; col < k; col++)
            if (solver.modelValue(row * k + col) == Minisat::l_True)
                vertex_cover.push_back(row);
    return vertex_cover;
}

vector<int> minimal(int approach) {
    int vertex_result[vertices];
    vector<int> minimal_vertex_cover;
    for(int i = 0; i< vertices; i++)
        vertex_result[i] = -1;

    // print CNF-SAT-VC
    if (approach == 0){
        for (int i = 0; i <= vertices; i++) {
            if(cnf_thread_timeout)
                break;
            Minisat::Solver solver;
            vertex_result[i] = cnf(solver, i);
            if (vertex_result[i]) {
                minimal_vertex_cover = get_vertex_cover(solver, i);
                return minimal_vertex_cover;
            }
        }
    }

    // print CNF-3-SAT-VC
    if (approach == 1){
        for (int i = 0; i <= vertices; i++) {
            if(cnf_3_thread_timeout)
                break;
            Minisat::Solver solver;
            vertex_result[i] = cnf_3(solver, i);
            if (vertex_result[i]) {
                minimal_vertex_cover = get_vertex_cover(solver, i);
                return minimal_vertex_cover;
            }
        }
    }
}

void print_set(set<int> s){
    int count = 0;
    for (auto it = s.begin(); it != s.end(); ++it) {
        cout << *it;
        if (++count != s.size()) {
            cout << " ";
        }
    }
    cout << endl;
}

void print_vector(vector<int> v){
    for(int i=0; i < v.size()-1; i++)
        cout << v[i] << " ";
    cout << v[v.size()-1] << endl;
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

void *cnf_thread_handler(void *arg){
    clockid_t clock_id;
    pthread_getcpuclockid(pthread_self(), &clock_id);

    timespec start_time{};
    cnf_thread_status = true;
    clock_gettime(clock_id, &start_time);

    cnf_result = minimal(0);

    if(!cnf_thread_timeout){
        timespec end_time{};
        clock_gettime(clock_id, &end_time);

        long long elapsed_us = (end_time.tv_sec - start_time.tv_sec) * 1000000LL + (end_time.tv_nsec - start_time.tv_nsec) / 1000LL;
        // printf("%lld\n", elapsed_us);
        //printf("CNF thread elapsed time: %lld us\n", elapsed_us);
        cnf_thread_status = false;
        pthread_exit(nullptr);
    }
    else{
        cnf_thread_status = false;
        pthread_exit(nullptr);
    }

}

void *cnf_3_thread_handler(void *arg){
    clockid_t clock_id;
    pthread_getcpuclockid(pthread_self(), &clock_id);

    timespec start_time{};
    cnf_3_thread_status = true;
    clock_gettime(clock_id, &start_time);

    cnf_3_result = minimal(1);

    if(!cnf_3_thread_timeout){
        timespec end_time{};
        clock_gettime(clock_id, &end_time);

        long long elapsed_us = (end_time.tv_sec - start_time.tv_sec) * 1000000LL + (end_time.tv_nsec - start_time.tv_nsec) / 1000LL;
        //printf("CNF-3 thread elapsed time: %lld us\n", elapsed_us);
        cnf_3_thread_status = false;
        pthread_exit(nullptr);
    }
    else{
        cnf_3_thread_status = false;
        pthread_exit(nullptr);
    }
}

void *vc_1_thread_handler(void *arg){
    clockid_t clock_id;
    pthread_getcpuclockid(pthread_self(), &clock_id);

    timespec start_time{};
    clock_gettime(clock_id, &start_time);

    vc1_result = approxvc1();

    timespec end_time{};
    clock_gettime(clock_id, &end_time);

    long long elapsed_us = (end_time.tv_sec - start_time.tv_sec) * 1000000LL + (end_time.tv_nsec - start_time.tv_nsec) / 1000LL;
     //printf("%lld\n", elapsed_us);
   // printf("VC-1 thread elapsed time: %lld us\n", elapsed_us);

    pthread_exit(nullptr);
}

void *refined_vc_1_thread_handler(void *arg){
    clockid_t clock_id;
    pthread_getcpuclockid(pthread_self(), &clock_id);

    timespec start_time{};
    clock_gettime(clock_id, &start_time);

    refined_vc1_result = refined_approxvc1();

    timespec end_time{};
    clock_gettime(clock_id, &end_time);

    long long elapsed_us = (end_time.tv_sec - start_time.tv_sec) * 1000000LL + (end_time.tv_nsec - start_time.tv_nsec) / 1000LL;
    //printf("%lld\n", elapsed_us);
   // printf("REFINED-VC-1 thread elapsed time: %lld us\n", elapsed_us);

    pthread_exit(nullptr);
}

void *vc_2_thread_handler(void *arg)
{
    clockid_t clock_id;
    pthread_getcpuclockid(pthread_self(), &clock_id);

    timespec start_time{};
    clock_gettime(clock_id, &start_time);
    vc2_result = approxvc2();

    timespec end_time{};
    clock_gettime(clock_id, &end_time);

    long long elapsed_us = (end_time.tv_sec - start_time.tv_sec) * 1000000LL + (end_time.tv_nsec - start_time.tv_nsec) / 1000LL;
    // printf("%lld\n", elapsed_us);
    //printf("VC-2 thread elapsed time: %lld us\n", elapsed_us);

    pthread_exit(nullptr);
}

void *refined_vc_2_thread_handler(void *arg)
{
    clockid_t clock_id;
    pthread_getcpuclockid(pthread_self(), &clock_id);

    timespec start_time{};
    clock_gettime(clock_id, &start_time);

    refined_vc2_result = refined_approxvc2();

    timespec end_time{};
    clock_gettime(clock_id, &end_time);

    long long elapsed_us = (end_time.tv_sec - start_time.tv_sec) * 1000000LL + (end_time.tv_nsec - start_time.tv_nsec) / 1000LL;
    //printf("REFINED-VC-2 thread elapsed time: %lld us\n", elapsed_us);
     //printf("%lld\n", elapsed_us);
    pthread_exit(nullptr);
}

void cnf_timeout_watcher(pthread_t thread_id, int time_limit)
{
    clockid_t cid;
    pthread_getcpuclockid(thread_id, &cid);
    struct timespec tspec;

    while (cnf_thread_status)
    {
        clock_gettime(cid, &tspec);
        if (tspec.tv_sec >= time_limit)
        {
            cout << "CNF-SAT-VC: timeout" << endl;
            cnf_thread_timeout = true;
            return;
        }
    }
}

void cnf_3_timeout_watcher(pthread_t thread_id, int time_limit)
{
    clockid_t cid;
    pthread_getcpuclockid(thread_id, &cid);
    struct timespec tspec;

    while (cnf_3_thread_status)
    {
        clock_gettime(cid, &tspec);
        if (tspec.tv_sec >= time_limit)
        {
            cout << "CNF-3-SAT-VC: timeout" << endl;
            cnf_3_thread_timeout = true;
            return;
        }
    }
}

void *input_output_thread_handler(void *arg) {
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
            split >> coordinate;
            if(coordinate == "{}")
                cout << "";
            else{
                get_edges(coordinate);

                pthread_create(&cnf_thread, nullptr, &cnf_thread_handler, nullptr);
                pthread_create(&cnf_3_thread, nullptr, &cnf_3_thread_handler, nullptr);
                pthread_create(&vc_1_thread, nullptr, &vc_1_thread_handler, nullptr);
                pthread_create(&refined_vc_1_thread, nullptr, &refined_vc_1_thread_handler, nullptr);
                pthread_create(&vc_2_thread, nullptr, &vc_2_thread_handler, nullptr);
                pthread_create(&refined_vc_2_thread, nullptr, &refined_vc_2_thread_handler, nullptr);

                cnf_timeout_watcher(cnf_thread, 5);
                cnf_3_timeout_watcher(cnf_3_thread, 5);

                pthread_join(cnf_thread, nullptr);
                pthread_join(cnf_3_thread, nullptr);
                pthread_join(vc_1_thread, nullptr);
                pthread_join(refined_vc_1_thread, nullptr);
                pthread_join(vc_2_thread, nullptr);
                pthread_join(refined_vc_2_thread, nullptr);

                /*    float cnf_num = cnf_result.size();
                    float vc1_num = vc1_result.size();
                    float vc2_num = vc2_result.size();
                    float rvc1_num = refined_vc1_result.size();
                    float rvc2_num = refined_vc2_result.size();
                    float vc1_ratio = vc1_num/cnf_num;
                    float vc2_ratio = vc2_num/cnf_num;
                    float rvc1_ratio = rvc1_num/cnf_num;
                    float rvc2_ratio = rvc2_num/cnf_num;*/
                if(!cnf_thread_timeout){
                    cout << "CNF-SAT-VC: ";
                    print_vector(cnf_result);
                }

                if(!cnf_3_thread_timeout){
                    cout << "CNF-3-SAT-VC: ";
                    print_vector(cnf_3_result);
                }
                cout << "APPROX-VC-1: ";
                print_set(vc1_result);
                cout << "APPROX-VC-2: ";
                print_vector(vc2_result);
                cout << "REFINED-APPROX-VC-1: ";
                print_set(refined_vc1_result);
                cout << "REFINED-APPROX-VC-2: ";
                print_vector(refined_vc2_result);
                /*cout << vc1_ratio << endl;
                cout << vc2_ratio << endl;
                cout << rvc1_ratio << endl;
                cout << "rvc2_ratio: " << rvc2_ratio << endl;*/
                cnf_thread_timeout = false;
                cnf_3_thread_timeout = false;
            }
        }
    }
    return nullptr;
}

int main() {
    int main_thread;
    pthread_create(&io_thread, nullptr, &input_output_thread_handler, nullptr);
    main_thread = pthread_join(io_thread, nullptr);
    if (main_thread){
        return 0;
    }
}