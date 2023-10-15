#include <bits/stdc++.h>

using namespace std;

const int START_STATE = 97;

int char_to_num(char ch){
    return int(ch) - 97;
}

set<int> set_difference(const set<int>& a, const set<int>& b) {
    set<int> diff;
    for (const int& elem : a) {
        if (b.find(elem) == b.end()) {
            diff.insert(elem);
        }
    }
    return diff;
}

set<int> set_intersection(const set<int>& a, const set<int>& b) {
    set<int> inter;
    for (const int& elem : a) {
        if (b.find(elem) != b.end()) {
            inter.insert(elem);
        }
    }
    return inter;
}

set<int> set_union(const set<int>& a, const set<int>& b) {
    set<int> uni = a;
    for (const int& elem : b) {
        uni.insert(elem);
    }
    return uni;
}

void print_equivalent_states(const vector<set<int>>& P) {
    cout << "Equivalent States:" << endl;
    for (const set<int>& eq_set : P) {
        if (eq_set.size() > 0) {  // Only print sets with more than one state
            cout << "{";
            for (auto it = eq_set.begin(); it != eq_set.end(); ++it) {
                cout << *it;
                if (next(it) != eq_set.end()) {
                    cout << ", ";
                }
            }
            cout << "}" << endl;
        }
    }
}

class DFA {
private:
    int num_a, num_s, init_s, num_f;
    vector<int> final_ss;
    vector<vector<vector<int>>> trans_to;
    vector<vector<int>> trans_counts;
    vector<char> alphabet;
    vector<int> states;

public:
    DFA(int num_a, int num_s, int init_s, int num_f, const vector<int>& final_ss, const vector<vector<string>>& trans_func) {
        this->num_a = num_a;
        this->num_s = num_s;
        this->init_s = init_s;
        this->num_f = num_f;
        this->final_ss = final_ss;
        for (int i=0; i < num_s;i++){
            this-> states.push_back(i);
        }

        trans_to.resize(num_s, vector<vector<int>>(num_a));
        for (const auto& trans : trans_func) {
            int st1 = stoi(trans[0]);
            char alph = trans[1][0];
            int st2 = stoi(trans[2]);
            trans_to[st1][char_to_num(alph)].push_back(st2);
        }
    }
    void print_transactions(){
        for (int i = 0; i < num_s; i++){
            if (find(states.begin(), states.end(), i) == states.end()) continue;
            for (int j = 0; j < num_a; j++){
                for (auto st2: trans_to[i][j]){
                    cout << i << " " << char(START_STATE + j) << " " << st2 << endl;
                }
            }
        }
    }
    void get_reachable_states(int v,
             vector<int> visited,
             vector<int>& result){
        result.push_back(v);
        for(int i=0; i < num_a; i ++){
            if (trans_to[v][i].size() == 0) continue;
            for (int st2: trans_to[v][i]){
                //tuple<int, int, int> state_f = tuple<int, int, int>(v, i, st2);
                if (find(visited.begin(), visited.end(), st2) == visited.end()){
                    vector<int> visited_n;
                    visited_n.insert(visited_n.begin(), visited.begin(), visited.end());
                    visited_n.push_back(st2);
                    get_reachable_states(st2, visited_n, result);
                }
            }
        }

    }
    void del_vertex(int v){
        cout << "To del: " << v << endl;
        auto it = find(states.begin(), states.end(), v);
        if (it != states.end()) {
            states.erase(it);
        }

        for(int i=0; i< num_s; i++){
            for(int j=0; j < num_a; j++){
                auto it = find(trans_to[i][j].begin(), trans_to[i][j].end(), v);
                if (it != trans_to[i][j].end()) trans_to[i][j].erase(it);
            }
        }
    }
    void del_unreachable(){
        vector<int> reachable;
        get_reachable_states(init_s, {}, reachable);
        int j = 0;
        for (int j=0; j < num_s; j++){
            if (find(states.begin(), states.end(), j) == states.end())  continue;
            if (find(reachable.begin(), reachable.end(), j) == reachable.end()) del_vertex(j);
        }
    }

    void del_dead(){
        vector<int> dead;
        for (int i=0; i < num_s; i++){
            if (i == init_s || find(final_ss.begin(), final_ss.end(), i) != final_ss.end()) continue;
            vector<int> reachable;
            get_reachable_states(i, {}, reachable);
            bool is_not_dead = false;
            for (int f: final_ss){
                if (find(reachable.begin(), reachable.end(), f) != reachable.end()){
                    is_not_dead = true;
                    break;
                }
            }
            if (!is_not_dead) dead.push_back(i);
        }

        for (int j=0; j < num_s; j++){
            if (find(states.begin(), states.end(), j) == states.end())  continue;
            if (find(dead.begin(), dead.end(), j) != dead.end()) del_vertex(j);
        }
    }

void unite_equivalent() {
    set<int> final_states(final_ss.begin(), final_ss.end());
    set<int> states_set(states.begin(), states.end());
    vector<set<int>> P = {final_states, set_difference(states_set, final_states)};

    queue<pair<set<int>, int>> W_queue;
    set<pair<set<int>, int>> W_set;

    for (int a=0; a < num_a; a++) {
        W_queue.push({final_states, a});
        W_queue.push({set_difference(states_set, final_states), a});
        W_set.insert({final_states, a});
        W_set.insert({set_difference(states_set, final_states), a});
    }

    while(!W_queue.empty()) {
        pair<set<int>, int> current_pair = W_queue.front(); W_queue.pop();
        set<int> A = current_pair.first;
        int a = current_pair.second;

        set<int> X;
        for (int s : states) {
            for (int t : trans_to[s][a]) {
                if (A.find(t) != A.end()) {
                    X.insert(s);
                    break;
                }
            }
        }

        // Refine the partition P with X
        vector<set<int>> newP;
        for (set<int> Y : P) {
            set<int> Y1 = set_intersection(Y, X);
            set<int> Y2 = set_difference(Y, X);
            if (!Y1.empty() && !Y2.empty()) {
                newP.push_back(Y1);
                newP.push_back(Y2);
                for (int b = 0; b < num_a; b++) {
                    pair<set<int>, int> new_pair = {Y, b};
                    if (W_set.find(new_pair) != W_set.end()) {
                        W_set.erase(new_pair);
                        W_queue.push({Y1, b});
                        W_queue.push({Y2, b});
                        W_set.insert({Y1, b});
                        W_set.insert({Y2, b});
                    } else {
                        if (Y1.size() <= Y2.size()) {
                            W_queue.push({Y1, b});
                            W_set.insert({Y1, b});
                        } else {
                            W_queue.push({Y2, b});
                            W_set.insert({Y2, b});
                        }
                    }
                }
            } else {
                newP.push_back(Y);
            }
        }
        P = newP;
    }
    print_equivalent_states(P);
    print_transitions_f(P);

}
void print_transitions_f(const vector<set<int>>& P) {
    cout << "Transitions between equivalent state sets:" << endl;

    for (const set<int>& from_set : P) {
        for (int a = 0; a < num_a; a++) {
            // Create a set to store states reachable by the current character 'a'
            set<int> reachable_states;

            for (int state : from_set) {
                for (int t : trans_to[state][a]) {
                    reachable_states.insert(t);
                }
            }

            // Check which equivalent state set the reachable states belong to
            for (const set<int>& to_set : P) {
                if (set_intersection(reachable_states, to_set).size() > 0) {
                    // Print the transition
                    cout << "{";
                    for (auto it = from_set.begin(); it != from_set.end(); ++it) {
                        cout << *it;
                        if (next(it) != from_set.end()) {
                            cout << ", ";
                        }
                    }
                    cout << "} {" << char(START_STATE + a) << "} {";
                    for (auto it = to_set.begin(); it != to_set.end(); ++it) {
                        cout << *it;
                        if (next(it) != to_set.end()) {
                            cout << ", ";
                        }
                    }
                    cout << "}" << endl;
                }
            }
        }
    }
}


};

struct DfaData {
    int num_a, num_s, init_s, num_f;
    vector<int> final_ss;
    vector<vector<string>> trans_func;
};

DfaData read_file(const string& filename) {
    ifstream file(filename);
    DfaData data;

    file >> data.num_a >> data.num_s >> data.init_s >> data.num_f;

    data.final_ss.resize(data.num_f);
    for (int i = 0; i < data.num_f; i++) {
        file >> data.final_ss[i];
    }

    string line;
    getline(file, line); // consume the newline character
    while (getline(file, line)) {
        vector<string> vec;
        size_t pos;
        while ((pos = line.find(' ')) != string::npos) {
            vec.push_back(line.substr(0, pos));
            line.erase(0, pos + 1);
        }
        vec.push_back(line);
        data.trans_func.push_back(vec);
    }

    return data;
}

int main() {
    DfaData data = read_file("input3.txt");

    DFA dfa(data.num_a, data.num_s, data.init_s, data.num_f, data.final_ss, data.trans_func);
    cout << "Initial transactions:" << endl;
    dfa.print_transactions();

    dfa.del_unreachable();
    dfa.del_dead();
    dfa.unite_equivalent();

    //cout << "Final transactions:" << endl;
    //dfa.print_transactions();

    //dfa.print_transitions_f();
    //dfa.get_all_words(true);
    return 0;
}
