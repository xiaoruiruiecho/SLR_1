#include <cstring>
#include <cassert>
#include <fstream>
#include <iostream>
#include <string>
#include <stack>
#include <queue>
#include <vector>
#include <map>
#include <set>
#include <unordered_map>
#include <algorithm>

#define tab "\t"
#define endl "\n"
#define fi first
#define se second
#define mst(arr, v) memset(arr, v, sizeof arr)
#define rep(i, a, b) for (int i = (a); i <= (b); i++)
#define dbg_vec(vec) for (auto & t: vec) { cout << t << " "; } cout << endl;
#define dbg_map(mp) for (auto & t: mp) cout << t.fi << ": " << t.se << endl;
#define dbg_set(st) for (auto & t: st) { cout << t << " "; } cout << endl;

using namespace std;
const char Empty = '$'; // '��'
const string EMPTY = "$"; // "��"
const char End = '#';
const string END = "#";
const int MAX_V_LEN = 2e2 + 10;
const int MAX_T_LEN = 2e2 + 10;
const int MAX_P_LEN = 4e2 + 10;
const int MAX_DFA_LEN = 1e2 + 10;

// �ķ���Ŀ��״̬
enum State {
    INITIAL = 0, // ��ʼ
        WAITING, // ��Լ
        REDUCED // ��Լ
};

// �ķ��е���Ŀ
struct Item {
    string V; // ��Ŀ���ķ��ս��
    vector < string > symbols; // ��Ŀ�Ҳ�ĸ�����
    int dot_pos; // ��Ŀ�Ҳ��λ��
    State state;

    bool operator == (const Item & t) const {
        if (t.V != V || t.dot_pos != dot_pos || t.state != state || t.symbols != symbols)
            return false;

        return true;
    }

    bool operator != (const Item & t) const {
        return !( * this == t);
    }
};

// DFA�е���Ŀ��
struct ItemSet {
    int idx;
    unordered_map < string, State > state; // WAITING || REDUCED
    vector < Item > items;
    vector < string > next_symbol; // �ɽ��ܵķ���
    unordered_map < string, int > next_dfa; // ���ܷ��ź�ת���Ӧ����Ŀ��
};


string grammar_filename, sentence_filename;
string S_ap, S; // �ع��ķ���ʼ���ţ��ķ���ʼ����
vector < string > Vs, Ts; // ���ս������ �ս������
set < string > First[MAX_V_LEN], Follow[MAX_V_LEN]; // ���ս���� First���� Follow��
vector < vector < string >> Ps[MAX_V_LEN]; // �����ս������Ĳ���ʽ����
vector < vector < string >> Ps_all;
unordered_map < int, string > P2V; // ����ʽ��Ӧ�������ս��
int Pcnt[MAX_V_LEN], sPcnt[MAX_V_LEN]; // ÿ�����ս���Ĳ���ʽ������ǰ׺��
unordered_map < string, int > V2idx, T2idx; // ���ս�������±��ӳ�䣨���Ⱥ�˳��
vector < Item > VItems[MAX_V_LEN]; // ���ս��������Ŀ������
int dfa_cnt; // DFA�еȼۼ��ĸ���
ItemSet DFA[MAX_DFA_LEN]; // ״̬ת��ͼ����
unordered_map < string, int > Action[MAX_DFA_LEN];
unordered_map < string, int > GoTo[MAX_DFA_LEN];


void Decorate(int size) {
    rep(i, 0, size)
    cout << "--------";
    cout << endl;
}


bool IsLetter(char c) {
    return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z';
}


bool IsChar(char c) {
    switch (c) {
        case '+':
        case '-':
        case '*':
        case '/':
        case ',':
        case ':':
        case '(':
        case ')':
        case '^':
        case '<':
        case '>':
        case '=':
        case '&':
        case '|':
        case '!':
        case '0':
        case '1':
        case '2':
        case '3':
        case '4':
        case '5':
        case '6':
        case '7':
        case '8':
        case '9':
        case Empty: // ��
            return true;

        default:
            if (c != ' ') {
                cout << "UnExpected Terminator " << c << " !" << endl;
                exit(0);
            }
            return false;
    }
}


bool IsDigit(char c) {
    return c >= '0' && c <= '9';
}


bool IsV(string symbol) {
    if (!symbol.size())
        return false;

    return symbol[0] >= 'A' && symbol[0] <= 'Z';
}


bool IsT(string symbol) {
    if (!symbol.size())
        return false;

    return !(symbol[0] >= 'A' && symbol[0] <= 'Z');
}


template < typename T > bool IsSubset(const set < T > & s1,
    const set < T > & s2) {
    for (auto & t: s2)
        if (!s1.count(t))
            return false;

    return true;
}


bool CanDeriveEmpty(string V) {
    for (auto & t: First[V2idx[V]]) {
        if (t == EMPTY)
            return true;
    }

    return false;
}


bool FindInVs(string symbol) {
    if (!symbol.size())
        return false;

    if (symbol == S_ap || V2idx[symbol])
        return true;
    return false;
}


bool FindInTs(string symbol) {
    if (!symbol.size())
        return false;

    if (Ts.size() && symbol == Ts[0] || T2idx[symbol])
        return true;
    return false;
}


bool FindInStrVec(const vector < string > & vec,
    const string & s) {
    return find(vec.begin(), vec.end(), s) != vec.end();
}


string Num2State(State s) {
    switch (s) {
        case INITIAL:
            return "��ʼ״̬";
        case WAITING:
            return "��Լ״̬";
        case REDUCED:
            return "��Լ״̬";
        default:
            return "����״̬";
    }
}


// ��ǰ״̬�ĺ��״̬
Item NextItem(const Item & item) {
    assert(item.state != REDUCED);

    Item next(item);
    next.state = (next.dot_pos < next.symbols.size() - 1) ? WAITING : REDUCED;
    next.dot_pos++;

    return next;
}


void DebugItem(const Item & item) {
    int dot_pos = item.dot_pos;
    cout << item.V << " " << Num2State(item.state) << ": " << item.V << " -> ";

    rep(i, 0, item.symbols.size() - 1) {
        if (i == dot_pos)
            cout << "�� ";
        cout << item.symbols[i] << " ";
    }

    if (dot_pos == (int) item.symbols.size())
        cout << "�� ";

    cout << endl;
}


void DebugItems(const vector < Item > & items) {
    for (auto & item: items)
        DebugItem(item);
}


void DebugVItems() {
    rep(i, 0, Vs.size() - 1)
    DebugItems(VItems[i]);
}


void DebugP() {
    rep(i, 0, Vs.size() - 1) {
        cout << i << ". " << Vs[i] << ": " << endl;
        cout << "�� " << Pcnt[i] << " ��" << endl;

        for (auto & t: Ps[i]) {
            string P = Vs[i] + " -> ";
            for (auto & s: t)
                P += s + " ";
            cout << P << endl;
        }

        cout << endl;
    }
}


void DebugFirst() {
    rep(i, 1, Vs.size() - 1) {
        cout << "Fisrt(" << Vs[i] << "): ";
        dbg_set(First[i]);
        cout << endl;
    }
}


void DebugFollow() {
    rep(i, 1, Vs.size() - 1) {
        cout << "Follow(" << Vs[i] << "): ";
        dbg_set(Follow[i]);
        cout << endl;
    }
}


void DebugDFA() {
    rep(i, 0, dfa_cnt) {
        cout << "I" << i << "��" << endl;
        cout << "----------------------------------------" << endl;
        for (auto & item: DFA[i].items)
            DebugItem(item);

        cout << endl << "�ɽ��ܷ���\t��һ״̬\n";
        for (auto & s: DFA[i].next_symbol)
            cout << s << tab << tab << DFA[i].next_dfa[s] << endl;
        cout << "----------------------------------------" << endl << endl;
    }
}


void DebugAction() {
    Decorate(Ts.size());
    cout << "| ";
    rep(i, 0, Ts.size() - 1)
    cout << tab << Ts[i];
    cout << tab << "|" << endl;

    rep(i, 0, dfa_cnt) {
        cout << "| I" << i << tab;
        rep(j, 0, Ts.size() - 1) {
            int action = Action[i][Ts[j]];
            if (action == -1)
                cout << "acc" << tab;
            else if (action != 0) {
                if (DFA[i].state[Ts[j]] == WAITING)
                    cout << "S" << action << tab;
                else if (DFA[i].state[Ts[j]] == REDUCED)
                    cout << "r" << action << tab;
            } else
                cout << " " << tab;
        }
        cout << "|" << endl;
    }

    Decorate(Ts.size());
}


void DebugGoTo() {
    Decorate(Vs.size() - 1);
    cout << "| ";
    rep(i, 1, Vs.size() - 1)
    cout << tab << Vs[i];
    cout << tab << "|" << endl;

    rep(i, 0, dfa_cnt) {
        cout << "| I" << i << tab;
        rep(j, 1, Vs.size() - 1) {
            int goto_idx = GoTo[i][Vs[j]];
            if (goto_idx)
                cout << goto_idx << tab;
            else
                cout << " " << tab;
        }
        cout << "|" << endl;
    }

    Decorate(Vs.size() - 1);
}


void DebugReduced(int action) {
    cout << P2V[action] << " -> ";
    dbg_vec(Ps_all[action]);
}


template < typename T > void DebugStack(stack < T > s) {
    stack < T > temp;

    while (s.size()) {
        temp.push(s.top());
        s.pop();
    }

    while (temp.size()) {
        cout << temp.top() << tab;
        temp.pop();
    }

    cout << endl;
}


// ����ǰ ���ս�� ��ӵ� ���ս��������
void AddV(string V) {
    if (find(Vs.begin(), Vs.end(), V) == Vs.end()) {
        V2idx[V] = Vs.size();
        Vs.push_back(V);
    }
}


// ����ǰ �ս�� ��ӵ� �ս��������
void AddT(string T) {
    if (find(Ts.begin(), Ts.end(), T) == Ts.end()) {
        T2idx[T] = Ts.size();
        Ts.push_back(T);
    }
}


// ����ǰ ����ʽ ��ӵ� ��Ӧ�ķ��ս���� ����ʽ������
void AddP(int V_idx, vector < string > P) {
    Ps[V_idx].push_back(P);
    Pcnt[V_idx]++;
}


void _AddVItem(int V_idx, string V, string sentence) {
    vector < string > symbols;

    int id1 = 0, id2 = 0, size = (int) sentence.size();
    while (id2 < size) {
        while (id1 < size && sentence[id1] == ' ')
            id1++;

        if (id1 >= size)
            break;

        id2 = id1;
        if (IsLetter(sentence[id1])) {
            while (id2 < size && (IsLetter(sentence[id2]) || IsDigit(sentence[id2])))
                id2++;
        } else if (IsChar(sentence[id1])) {
            while (id2 < size && IsChar(sentence[id2]))
                id2++;
        }

        string symbol = sentence.substr(id1, id2 - id1);
        // cout << symbol << endl;
        if (IsT(symbol)) // ���ս��
            AddT(symbol);
        symbols.push_back(symbol);

        id1 = id2;
    }

    AddP(V_idx, symbols);

    // cout << symbols.size() << endl;
    rep(i, 0, symbols.size()) {
        Item item = {
            V,
            symbols,
            i
        };

        if (i == 0)
            item.state = INITIAL;
        else if (i == (int) symbols.size())
            item.state = REDUCED;
        else
            item.state = WAITING;

        VItems[V_idx].push_back(item);
    }

    // cout << "_AddVItem over" << endl << endl;
}


// ���ս���±� ����ʽ����
void AddVItem(int V_idx, string P) {
    cout << "(" << V_idx << ", " << Vs[V_idx] << "): " << P << endl;

    int idx = 0, size = P.size();
    while (idx < size && P[idx] != '>') // TO FIX: != "->"
        idx++;
    idx++;

    while (idx < size) {
        string sentence;
        while (idx < size) // && P[idx] != '|'
        {
            if (P[idx] == '\"') {
                while (++idx < size && P[idx] != '\"')
                    sentence += P[idx];
                idx++;
            } else
                sentence += P[idx], idx++;
        }


        // cout << sentence << endl;
        _AddVItem(V_idx, Vs[V_idx], sentence);
        idx++;
    }

    cout << "�ù��������ϣ�" << endl << endl;
}


void InitBroadenGrammar(string S) {
    S_ap = "S\'";
    AddV(S_ap);

    string P = S_ap + " -> " + S;
    AddVItem(V2idx[S_ap], P);
}


void InitPs() {
    sPcnt[0] = Pcnt[0];
    rep(i, 1, Vs.size() - 1)
    sPcnt[i] = sPcnt[i - 1] + Pcnt[i];

    rep(i, 0, Vs.size() - 1) {
        for (auto & s: Ps[i]) {
            //            dbg_vec(s); cout << endl;
            P2V[Ps_all.size()] = Vs[i];
            Ps_all.push_back(s);
        }
    }
}


void InitGrammar(string filename) {
    cout << endl << "���ڼ���" << filename << "...................." << endl << endl;

    ifstream fin;
    fin.open(filename, ios::in);
    if (!fin.is_open()) {
        cout << filename << "�ļ������ڣ�����" << endl;
        exit(0);
    }

    string buffer;
    while (getline(fin, buffer)) {
        cout << "��ǰ������ͣ�" << buffer << endl;

        int size = (int) buffer.size();
        if (size < 3)
            continue;
        string V;

        int idx = 0, idx2 = 0;
        while (idx < size && buffer[idx] != ' ')
            V += buffer[idx], idx++;
        // cout << V << endl;

        if (S == "") {
            S = V;
            InitBroadenGrammar(S);
        }

        if (!FindInVs(V))
            AddV(V);

        while (idx < size && buffer[idx++] != '>');

        while (idx < size && idx2 < size) {
            idx2 = idx;
            while (idx2 < size && buffer[idx2] != '|')
                idx2++;

            // TO FIX: more pairs of \" \"
            if (idx2 > 0 && buffer[idx2 - 1] == '\"') {
                while (idx2 < size && buffer[idx2] != '\"')
                    idx2++;
                while (idx2 < size && buffer[idx2] != '|')
                    idx2++;
            } else if (idx2 > 0 && buffer[idx2 - 1] != '\"' && idx2 + 1 < size && buffer[idx2 + 1] == '|') {
                //            	cout << "\"||\" Ӧ�� ˫���Ű�ס���������޸��ķ�������" << endl;
                //				exit(0);
                idx2 += 2;
                while (idx2 < size && buffer[idx2] != '|')
                    idx2++;
            }

            // cout << "idx " << idx << ", idx2 " << idx2 << endl;
            string substr = buffer.substr(idx, idx2 - idx);
            string P = V + " -> " + substr;
            AddVItem(V2idx[V], P);

            idx = idx2 + 1;
        }

        cout << endl;
    }

    AddT(END);

    InitPs();

    // ���ս������
    cout << endl << "���ս����������" << endl;
    dbg_vec(Vs);
    cout << endl;
    //    dbg_map(V2idx);
    // �ս������
    cout << endl << "�ս����������" << endl;
    dbg_vec(Ts);
    cout << endl;
    //    dbg_map(T2idx);

    cout << endl << "����ʽ��������" << endl;
    DebugP();

    cout << endl << "��Ŀ��������" << endl;
    DebugVItems();

    cout << endl << endl;
}


template < typename T > void UnionSet(set < T > & s1, set < T > & s2) {
    set_union(s1.begin(), s1.end(), s2.begin(), s2.end(), inserter(s1, s1.begin()));
}


void InitFirst() {
    bool can_stop = false;
    int size = (int) Vs.size();
    int first_loop_time = 0;

    while (!can_stop) {
        if (++first_loop_time > 100) {
            cout << "��ʼ�� First��ʧ�ܣ�����" << endl << endl;
            exit(0);
        }

        can_stop = true;

        //        cout << first_loop_time << endl;

        rep(i, 1, size - 1) {
            for (auto & t: Ps[i]) {
                //                cout << Vs[i] << ": ";
                //                dbg_vec(t);

                if (!t.size())
                    continue;

                if (!FindInVs(t[0])) // �ս�������뵽 First����
                {
                    if (!First[i].count(t[0])) {
                        First[i].insert(t[0]); // ���ս������ First�����뵽 ��ǰ���ս���� First����
                        can_stop = false;
                    }
                } else {
                    int j = 0;

                    while (j < t.size()) {
                        string next = t[j];

                        if (!IsSubset(First[i], First[V2idx[next]])) {
                            // set_union(First[i].begin(), First[i].end(), First[V2idx[t[j]]].begin(), First[V2idx[t[j]]].end(), inserter(First[i], First[i].begin()));
                            UnionSet(First[i], First[V2idx[next]]);
                            can_stop = false;
                        }

                        j++;

                        if (!CanDeriveEmpty(next)) // t[j] -/> ��
                            break;
                    }
                }

                //                DebugFirst();
            }
        }
    }

    cout << "First�����£�" << endl;
    Decorate(8);
    DebugFirst();
    Decorate(8);
    cout << endl;
}


void InitFollow() {
    Follow[V2idx[S]].insert(END);

    bool can_stop = false;
    int follow_loop_time = 0;

    while (!can_stop) {
        //        cout << follow_loop_time << endl;
        if (++follow_loop_time > 100) {
            cout << "��ʼ�� Follow��ʧ�ܣ�����" << endl << endl;
            exit(0);
        }

        can_stop = true;

        rep(i, 1, Vs.size() - 1) {
            for (auto & t: Ps[i]) {
                //                cout << Vs[i] << " -> ";
                //                dbg_vec(t);

                int size = (int) t.size();
                rep(j, 0, size - 1) {
                    const string & s = t[j];
                    int V_idx = V2idx[s];

                    if (FindInVs(s)) {
                        if (j == size - 1) // A -> ��B
                        {
                            if (!IsSubset(Follow[V_idx], Follow[i])) {
                                UnionSet(Follow[V_idx], Follow[i]); // V1 & V2 can't be the same
                                can_stop = false;
                            }
                        } else // A -> ��B(C?��)...
                        {
                            int k = j + 1;

                            while (k < size) {
                                string next = t[k];
                                int next_idx = V2idx[t[k]];

                                if (!FindInVs(next)) // A -> ��B��...
                                {
                                    if (!Follow[V_idx].count(next)) {
                                        Follow[V_idx].insert(next);
                                        can_stop = false;
                                    }
                                    break;
                                } else // A -> ��BC...
                                {
                                    if (!CanDeriveEmpty(next)) // C -/> ��
                                    {
                                        if (!IsSubset(Follow[V_idx], First[next_idx])) {
                                            UnionSet(Follow[V_idx], First[next_idx]);
                                            can_stop = false;
                                        }
                                        break;
                                    } else // C -> ��
                                    {
                                        set < string > temp(First[next_idx]);
                                        temp.erase(EMPTY);

                                        if (!IsSubset(Follow[V_idx], temp)) {
                                            UnionSet(Follow[V_idx], temp);
                                            can_stop = false;
                                        }

                                        if (k == size - 1) {
                                            if (!IsSubset(Follow[V_idx], Follow[i])) {
                                                UnionSet(Follow[V_idx], Follow[i]);
                                                can_stop = false;
                                            }
                                            break;
                                        } else {
                                            // don't break
                                        }
                                    }
                                }

                                k++;
                            }
                        }
                    }
                }

                //                DebugFollow();
            }
        }
    }

    cout << "Follow�����£�" << endl;
    Decorate(8);
    DebugFollow();
    Decorate(8);
    cout << endl;
}


// ��� items�Ƿ���֮ǰĳ��״̬ͼ���ϵ��Ӽ�
int FindItem(const vector < Item > & items, int dfa_cnt) {
    rep(i, 0, dfa_cnt) {
        bool flag1 = true;
        for (auto & item: items) {
            bool flag2 = false;
            for (auto & t: DFA[i].items) {
                if (t == item) {
                    flag2 = true;
                    break;
                }
            }

            if (!flag2) {
                flag1 = false;
                break;
            }
        }

        if (flag1)
            return i;
    }

    return -1;
}


// �����ս�� V�����г�ʼ̬����ʽ���뵽��Ŀ������
void AddInitialP(string V, int dfa_idx) {
    int V_idx = V2idx[V];

    for (auto t: VItems[V_idx]) {
        if (t.state == INITIAL) {
            DFA[dfa_idx].items.push_back(t);

            // TO CONSIDER: death loop!!!
            if (t.symbols.size() && !FindInStrVec(DFA[dfa_idx].next_symbol, t.symbols[0])) {
                DFA[dfa_idx].next_symbol.push_back(t.symbols[0]);

                bool exist = FindInVs(t.symbols[0]); // TODO: if t.symbol is really a V ?
                if (IsV(t.symbols[0]) && exist)
                    AddInitialP(t.symbols[0], dfa_idx);
            }
        }
    }
}


void InitDFA() {
    cout << endl << "���ڹ��� LR(0) DFA...................." << endl;

    dfa_cnt = 0;
    DFA[0].idx = dfa_cnt;
    AddInitialP(S_ap, dfa_cnt);

    queue < ItemSet > q;
    q.push(DFA[dfa_cnt]);

    while (q.size()) {
        auto t = q.front();
        q.pop(); // pop������Ͳ��� auto &
        int cur_dfa_idx = t.idx;

        //        cout << endl << "next_symbol.size()��" << t.next_symbol.size() << endl;
        //        cout << "items.size()��" << t.items.size() << endl;
        //        cout << "cur_dfa_idx��" << cur_dfa_idx << endl;

        for (auto & symbol: t.next_symbol) {
            vector < Item > items; // ���� symbol���ܽ������һ��Ŀ����
            for (auto & item: t.items) {
                if (item.dot_pos < item.symbols.size() && item.symbols[item.dot_pos] == symbol)
                    items.push_back(NextItem(item));
            }

            //            cout << symbol << endl;
            //            DebugItems(items);

            int dfa_idx = FindItem(items, dfa_cnt);
            if (dfa_idx == -1) {
                dfa_cnt++;
                //                cout << "---------- need_new_dfa��I" << dfa_cnt << " ----------" << endl;
                ItemSet & item_set = DFA[dfa_cnt];
                item_set.idx = dfa_cnt;

                for (auto item: items) {
                    item_set.items.push_back(item);

                    if (item.dot_pos < item.symbols.size() && !FindInStrVec(item_set.next_symbol, item.symbols[item.dot_pos]))
                        item_set.next_symbol.push_back(item.symbols[item.dot_pos]);

                    if (item.dot_pos < item.symbols.size() && IsV(item.symbols[item.dot_pos]))
                        AddInitialP(item.symbols[item.dot_pos], dfa_cnt);
                }

                //                DebugItems(item_set.items);
                DFA[cur_dfa_idx].next_dfa[symbol] = dfa_cnt;
                //                cout << "I" << cur_dfa_idx << " --" << symbol << "-->" << " I" << dfa_cnt << endl;
                q.push(item_set);
                //                cout << "----------q.push(item_set);----------" << endl << endl;
            } else {
                DFA[cur_dfa_idx].next_dfa[symbol] = dfa_idx; // ����֮ǰ�Ѵ��ڵ�״̬
                //                cout << "I" << cur_dfa_idx << " --" << symbol << "-->" << " I" << dfa_idx << endl;
            }
        }
    }

    cout << endl << "DFA״̬ͼ������" << dfa_cnt + 1 << endl << endl;
    DebugDFA();

    cout << endl << "LR(0) DFA������ɣ�����" << endl;
}


// �ж����������Ƿ��н���
bool HasIntersection(const set < string > & s1,
    const set < string > & s2) {
    for (const auto & elem: s1) {
        if (s2.find(elem) != s2.end()) {
            return true;
        }
    }

    return false;
}


// �ж�һ�鼯���Ƿ����������ཻ
bool AreSetsDoNotIntersectEachOther(const vector < set < string >> & sets) {
    int n = sets.size();
    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) {
            if (HasIntersection(sets[i], sets[j])) {
                return false;
            }
        }
    }

    return true;
}


int GetReducedIdx(int V_idx,
    const vector < string > & P) {
    int reduced_idx = (V_idx == 0) ? 0 : sPcnt[V_idx - 1];

    for (auto & item: Ps[V_idx]) {
        if (item == P)
            break;
        else
            reduced_idx++;
    }

    return reduced_idx;
}


void InitAction() {
    cout << endl << "���ڹ��� LR(0) Action��...................." << endl << endl;

    rep(i, 0, dfa_cnt) {
        //        cout << endl;
        //        cout <<  "���� I" << i << "�� Action��...................." << endl;
        //        DebugItems(DFA[i].items);

        int reduced_cnt = 0;
        Item reduced_item;

        vector < string > Bs(1);
        vector < Item > B_reduced_items(1);
        vector < set < string >> alphas_followB(1);
        unordered_map < string, bool > is_V_exist;

        for (auto & t: DFA[i].items) {
            if (t.state == REDUCED) {
                reduced_item = t, reduced_cnt++;
                if (!is_V_exist[t.V]) {
                    Bs.push_back(t.V); // TO CONSIDER: �Ƿ���� ��ͬ���ս�� �Ƶ����� ��ͬ��Լ�� ???
                    B_reduced_items.push_back(t);
                    alphas_followB.push_back(Follow[V2idx[t.V]]);
                    is_V_exist[t.V] = true;
                }
            } else {
                alphas_followB[0].insert(t.symbols[t.dot_pos]);
            }
        }

        bool has_intersection = !AreSetsDoNotIntersectEachOther(alphas_followB) && (Bs.size() == B_reduced_items.size());

        if (reduced_cnt > 0 && reduced_cnt < DFA[i].items.size() || reduced_cnt > 1 && reduced_cnt == DFA[i].items.size()) {
            bool state_flag = false; // true: �ƽ�����������Լ��ͻ; false: ��Լ����������Լ��ͻ;
            if (reduced_cnt < DFA[i].items.size())
                state_flag = true;

            auto print_error = [state_flag](int i, string detail) {
                if (state_flag)
                    cout << "״̬�� I" << DFA[i].idx << " " + detail + "�ƽ�����������Լ��ͻ��" << endl;
                else
                    cout << "״̬�� I" << DFA[i].idx << " " + detail + "��Լ����������Լ��ͻ��" << endl;
            };

            print_error(i, "����");

            DebugItems(DFA[i].items);
            cout << endl << "���ķ����� LR(0) �ķ�������" << endl;
            cout << "���Թ��� SLR(1) �ķ�...................." << endl << endl;

            if (has_intersection) {
                cout << "���� {��_1, ��_2, ..., ��_m}, Follow(B_1), Follow(B_2), ...Follow(B_n) �����������ཻ������" << endl;
                if (state_flag)
                    cout << "���ķ��޷������ƽ�����������Լ��ͻ��Ҳ���� SLR(1) �ķ�������" << endl << endl;
                else
                    cout << "���ķ��޷������Լ����������Լ��ͻ��Ҳ���� SLR(1) �ķ�������" << endl << endl;
                exit(0);
            }

            bool flag = false;
            for (auto t: Ts) {
                if (alphas_followB[0].count(t)) {
                    Action[DFA[i].idx][t] = DFA[i].next_dfa[t];
                    DFA[i].state[t] = WAITING;

                    flag = true;
                } else {
                    rep(j, 1, alphas_followB.size() - 1) {
                        if (alphas_followB[j].count(t)) {
                            int reduced_idx = GetReducedIdx(V2idx[Bs[j]], B_reduced_items[j].symbols);

                            Action[DFA[i].idx][t] = reduced_idx;
                            DFA[i].state[t] = REDUCED;

                            flag = true;
                        }
                    }
                }
            }

            if (!flag) {
                print_error(i, "�޷�����");
                exit(0);
            } else {
                cout << "����ɹ�������" << endl << endl;
            }
        } else if (reduced_cnt == 1) // ��Լ̬
        {
            int V_idx = V2idx[reduced_item.V];
            int reduced_idx = (V_idx == 0) ? 0 : sPcnt[V_idx - 1];
            //            cout << reduced_item.V << " " << V_idx << " " << reduced_idx << endl;

            //            if(V_idx == 0) // S' -> S
            //            {
            //                Action[DFA[i].idx]["#"] = -1;
            //                continue;
            //            }

            for (auto & item: Ps[V_idx]) {
                //                dbg_vec(item);
                //                dbg_vec(reduced_item.symbols);
                //                cout << (item == reduced_item.symbols) << endl << endl;
                if (item == reduced_item.symbols) // if(item != reduced_item.symbols)
                    break;
                else
                    reduced_idx++;
            }

            //            cout << DFA[i].idx << " " << reduced_idx << endl;
            for (auto t: Ts) // ��ȡ�ƽ�����
            {
                Action[DFA[i].idx][t] = reduced_idx;
                DFA[i].state[t] = REDUCED;
            }
        } else {
            for (auto s: DFA[i].next_symbol)
                if (IsT(s)) {
                    Action[DFA[i].idx][s] = DFA[i].next_dfa[s];
                    DFA[i].state[s] = WAITING;
                }
        }
    }

    // TO FIX: may not be 1
    Action[1][END] = -1;
    DFA[1].state[END] = REDUCED;

    cout << endl << endl;

    DebugAction();
    cout << endl << "Action������ɣ�����\n���ķ��� SLR(1) �ķ�������" << endl;
}


void InitGoTo() {
    cout << endl << "���ڹ��� SLR(1) GoTo��...................." << endl;

    rep(i, 0, dfa_cnt)
    for (auto s: DFA[i].next_symbol)
        if (IsV(s))
            GoTo[DFA[i].idx][s] = DFA[i].next_dfa[s];

    DebugGoTo();
    cout << endl << "GoTo������ɣ�����" << endl << endl << endl;
}


void GetInput(stack < string > & input_stack, ifstream & fin) {
    stack < string > temp;
    string symbol;

    while (fin >> symbol)
        temp.push(symbol);
    temp.push("#");

    while (temp.size()) {
        input_stack.push(temp.top());
        temp.pop();
    }
}


void GrammarAnalyze(string filename) {
    cout << endl << "���ڷ���" << filename << "...................." << endl << endl;

    ifstream fin;
    fin.open(filename, ios::in);
    if (!fin.is_open()) {
        cout << filename << "�ļ������ڣ�����" << endl;
        exit(0);
    }

    stack < int > state_stack;
    stack < string > symbol_stack;
    stack < string > input_stack;
    state_stack.push(0);
    symbol_stack.push(END);
    GetInput(input_stack, fin);

    string symbol;
    int empty_input_time = 0, total_time = 0;
    while (!input_stack.empty()) {
        symbol = input_stack.top();
        cout << ++total_time << ". " << symbol << ": " << endl;
        Decorate(5);

        int top = state_stack.top();
        int action = Action[top][symbol];

        //        cout << top << " " << action << " " << empty_input_time << endl;

        if (DFA[top].state[symbol] == WAITING || DFA[top].state[symbol] == INITIAL) {
            // TO CONSIDER: death loop ?
            if (action == 0) // ���Է�һ���մ�
            {
                if (++empty_input_time > 5) {
                    cout << "�þ��������޷�����������" << endl;
                    exit(0);
                }

                cout << "S" << Action[top][EMPTY] << endl;
                state_stack.push(Action[top][EMPTY]);
                symbol_stack.push(EMPTY);
            } else {
                cout << "S" << action << endl;
                state_stack.push(action);
                symbol_stack.push(symbol);
                input_stack.pop();

                empty_input_time = 0;
            }
        } else if (DFA[top].state[symbol] == REDUCED) {
            if (action == -1) {
                cout << "acc\n�����ɹ�������" << endl;
                return;
            } else
                cout << "r" << action << endl;
            DebugReduced(action);

            int size = Ps_all[action].size();
            rep(i, 1, size) {
                symbol_stack.pop();
                state_stack.pop();
            }

            int go_to = GoTo[state_stack.top()][P2V[action]];
            cout << "Goto" << go_to << endl;
            symbol_stack.push(P2V[action]);
            state_stack.push(go_to);

            empty_input_time = 0;
        }

        cout << endl;
        cout << "״̬ջ\t";
        DebugStack(state_stack);
        cout << "����ջ\t";
        DebugStack(symbol_stack);
        Decorate(symbol_stack.size());
        cout << endl;
    }
}


int main() {
    cout << "�����ķ�������ļ����ƣ������ļ���׺������";
    cin >> grammar_filename;
    // grammar_filename = "SLR_Grammar.txt";

    InitGrammar(grammar_filename);

    InitFirst();

    InitFollow();

    InitDFA();

    InitAction();

    InitGoTo();

    cout << "������Ҫ�������ӵ��ļ����ƣ������ļ���׺������";
    while (cin >> sentence_filename) {
        GrammarAnalyze(sentence_filename);
        cout << endl << "������Ҫ�������ӵ��ļ����ƣ������ļ���׺������";
    }
    // sentence_filename = "SLR_Sentence_5.txt";

    return 0;
}


// Grammar.txt
// Sentence.txt
