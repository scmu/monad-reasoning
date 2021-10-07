#include <iostream>
#include <stack>
#include <vector>
#include <unistd.h>
#include <chrono>
using namespace std;
using namespace std::chrono;

void print(vector<int> v) {
  for (auto i : v) cout << i << ", ";
  cout << "\n";
}

bool safe(int q, int n, vector<int> qs) {
  if (qs.empty()) return true;
  int q1 = *(qs.end() - 1);
  qs.pop_back();
  return q != q1 && q != q1+n && q != q1-n && safe(q, n+1, qs);
}

bool valid(vector<int> qs) {
  if (qs.empty()) return true;
  int q = *(qs.end() - 1);
  qs.pop_back();
  return valid(qs) && safe(q, 1, qs);
}


vector<vector<int> > ans;

struct State {
  int c;
  vector<int> sol;
  State () {}
  State(int c, const vector<int> &sol): c(c), sol(sol) {}
  void plus(int r) {
    c++;
    sol.push_back(r);
  }
  void minus(int r) {
    c--;
    sol.pop_back();
  }
};

// local-state semantics
// void queensLocal(vector<vector<int> > &ans, int n, int c, vector<int> sol) {
void queensLocal(vector<vector<int> > &ans, int n, State st) {
  if (st.c >= n) ans.push_back(st.sol);
  else for (int r = 1; r <= n; r++) {
    auto cur = st;
    cur.plus(r);
    if (valid(cur.sol)) {
      queensLocal(ans, n, cur);
    }
  }
}

State stGlobal;
void queensGlobal(vector<vector<int> > &ans, int n) {
  if (stGlobal.c >= n) ans.push_back(stGlobal.sol);
  else for (int r = 1; r <= n; r++) {
    auto tmp = stGlobal; // using immutable state
    stGlobal.plus(r);
    if (valid(stGlobal.sol)) {
      queensGlobal(ans, n);
    }
    stGlobal = tmp;
  }
}


State stModify;
void queensModify(vector<vector<int> > &ans, int n) {
  if (stModify.c >= n) ans.push_back(stModify.sol);
  else for (int r = 1; r <= n; r++) {
    stModify.plus(r);
    if (valid(stModify.sol)) {
      queensModify(ans, n);
    }
    stModify.minus(r); // mutable state
  }
}

struct State2 {
  // State *s;
  short r;
  bool isminus; 
  State2(short r, bool b): r(r), isminus(b) {}
  // State2(State *s, int r, bool b): s(s), r(r), ispop(b) {}
};

stack<State2> st;
State stStack = State(0, vector<int>());
const State2 onefalse = State2(1, false);

stack<State2> push(State2 x) {
  st.push(x);
  return st;
}

void queensStateR(vector<vector<int> > &ans, int n) {
  st.push(State2(1, false));
  while (!st.empty()) {
    State2 cur = st.top(); st.pop();
    if (cur.isminus) {
      stStack.minus(cur.r);
      continue;
    }
    if (stStack.c >= n) ans.push_back(stStack.sol);
    else {
      if (cur.r < n) st = push(State2(cur.r+1, false));
      short t = cur.r;
      stStack.plus(t);
      // cur.r = 1;
      if (valid(stStack.sol)) {
        st = push(State2(t, true));
        // st.push(cur);
        st = push(onefalse);
      }
      else stStack.minus(t); // doesn't matter
    }
  }
}

void queensStackR(vector<vector<int> > &ans, int n) {
  st.push(State2(1, false));
  while (!st.empty()) {
    State2 cur = st.top(); st.pop();
    if (cur.isminus) {
      stStack.minus(cur.r);
      continue;
    }
    if (stStack.c >= n) ans.push_back(stStack.sol);
    else {
      if (cur.r < n) st.push(State2(cur.r+1, false));
      short t = cur.r;
      stStack.plus(t);
      // cur.r = 1;
      if (valid(stStack.sol)) {
        st.push(State2(t, true));
        // st.push(cur);
        st.push(onefalse);
      }
      else stStack.minus(t); // doesn't matter
    }
  }
}

/*
struct State2 {
  int c, r;
  vector<int> sol;
  State2 () {}
  State2(const int &c, const int &r, const vector<int> &sol): c(c), r(r), sol(sol) {}
  void plus(int r) {
    c++;
    sol.push_back(r);
  }
  void minus(int r) {
    c--;
    sol.pop_back();
  }
};

stack<State2> st;
void queensStackR(vector<vector<int> > &ans, int n) {
  st.push(State2(0, 1, vector<int>()));
  while (!st.empty()) {
    // if (st.size() > 9) printf("hi");
    State2 cur = st.top(); st.pop();
    if (cur.c >= n) ans.push_back(cur.sol);
    else {
      if (cur.r < n) {
        cur.r ++;
        st.push(cur);
        cur.r --;
      }
      // int t = cur.r;
      cur.plus(cur.r);
      cur.r = 1;
      if (valid(cur.sol)) {
        st.push(cur);
      }
    }
  }
}
*/

// ------------------------------------------------------------------------------
int testnum = 1;

void test1(int n) {
  auto t1 = high_resolution_clock::now();

  for (int t = 1; t <= testnum; t ++) {
    ans.clear();
    queensLocal(ans, n, State(0, vector<int>()));
  }

  auto t2 = high_resolution_clock::now();
  duration<double, milli> ms_double = t2 - t1;
  printf("queensLocal %d %lf\n", (int) ans.size(), (ms_double.count() / 1000) / testnum);
}

void test2(int n) {
  auto t1 = high_resolution_clock::now();

  for (int t = 1; t <= testnum; t ++) {
    ans.clear();
    stGlobal = State(0, vector<int>());
    queensGlobal(ans, n);
  }

  auto t2 = high_resolution_clock::now();
  duration<double, milli> ms_double = t2 - t1;
  printf("queensGlobal %d %lf\n", (int) ans.size(), (ms_double.count() / 1000) / testnum);
}

void test3(int n) {
  auto t1 = high_resolution_clock::now();

  for (int t = 1; t <= testnum; t ++) {
    ans.clear();
    stModify = State(0, vector<int>());
    queensModify(ans, n);
  }

  auto t2 = high_resolution_clock::now();
  duration<double, milli> ms_double = t2 - t1;
  printf("queensModify %d %lf\n", (int) ans.size(), (ms_double.count() / 1000) / testnum);
}

void test4(int n) {
  auto t1 = high_resolution_clock::now();

  for (int t = 1; t <= testnum; t ++) {
    ans.clear();
    st = stack<State2>();
    stStack = State(0, vector<int>());
    queensStateR(ans, n);
  }

  auto t2 = high_resolution_clock::now();
  duration<double, milli> ms_double = t2 - t1;
  printf("queensStateR %d %lf\n", (int) ans.size(), (ms_double.count() / 1000) / testnum);
}

void test5(int n) {
  auto t1 = high_resolution_clock::now();

  for (int t = 1; t <= testnum; t ++) {
    ans.clear();
    st = stack<State2>();
    stStack = State(0, vector<int>());
    queensStackR(ans, n);
  }

  auto t2 = high_resolution_clock::now();
  duration<double, milli> ms_double = t2 - t1;
  printf("queensStackR %d %lf\n", (int) ans.size(), (ms_double.count() / 1000) / testnum);
}



int main() {
  int n = 11;
  // cin >> n;

  test1(n);
  test2(n);
  test3(n);
  test4(n);
  test5(n);

  // queensGlobal(ans, 4);
  ans.clear();
  queensStackR(ans, 4);
  st = stack<State2>();
  stStack = State(0, vector<int>());
  for (auto v : ans) print(v);
}

/*
n=11:
queensLocal 2680 7.941035
queensGlobal 2680 7.577763
queensModify 2680 7.292723
queensStateR 2680 7.734149
queensStackR 2680 7.238383
*/


