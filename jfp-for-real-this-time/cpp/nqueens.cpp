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
void queensLocal(vector<vector<int> > &ans, int n, State st) { // new state for every branch
  if (st.c >= n) ans.push_back(st.sol);
  else for (int r = 1; r <= n; r++) {
    auto cur = st;
    cur.plus(r);
    if (valid(cur.sol)) {
      queensLocal(ans, n, cur);
    }
  }
}
void queensLocalW(int n) {
  ans.clear();
  queensLocal(ans, n, State(0, vector<int>()));
}

State stGlobal;
void queensGlobal(vector<vector<int> > &ans, int n) {
  if (stGlobal.c >= n) ans.push_back(stGlobal.sol);
  else for (int r = 1; r <= n; r++) {
    auto tmp = stGlobal;
    stGlobal.plus(r);
    if (valid(stGlobal.sol)) {
      queensGlobal(ans, n);
    }
    stGlobal = tmp; // immutable state
  }
}
void queensGlobalW(int n) {
    ans.clear();
    stGlobal = State(0, vector<int>());
    queensGlobal(ans, n);
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
void queensModifyW(int n) {
    ans.clear();
    stModify = State(0, vector<int>());
    queensModify(ans, n);
}


struct State2 {
  short r;
  bool isminus; // true: minus instruction; false: search rows r...n
  State2(short r, bool b): r(r), isminus(b) {}
};

stack<State2> st;
State stStack = State(0, vector<int>());
const State2 onefalse = State2(1, false);

stack<State2> push(State2 x) {
  st.push(x);
  return st;
}
stack<State2> pop() {
  st.pop();
  return st;
}

void queensState(vector<vector<int> > &ans, int n) {
  st.push(State2(1, false));
  while (!st.empty()) {
    State2 cur = st.top(); st = pop(); // immutable
    if (cur.isminus) {
      stStack.minus(cur.r);
      continue;
    }
    if (stStack.c >= n) ans.push_back(stStack.sol);
    else {
      short t = cur.r;
      if (t < n) st = push(State2(t+1, false)); // immutable
      auto tmp = stStack;
      stStack.plus(t);
      if (valid(stStack.sol)) {
        st = push(State2(t, true)); // immutable
        st = push(onefalse); // immutable
      }
      else stStack = tmp; // immutable
    }
  }
}
void queensStateW(int n) {
    ans.clear();
    st = stack<State2>();
    stStack = State(0, vector<int>());
    queensState(ans, n);
}


void queensStateR(vector<vector<int> > &ans, int n) {
  st.push(State2(1, false));
  while (!st.empty()) {
    State2 cur = st.top(); st = pop(); // immutable
    if (cur.isminus) {
      stStack.minus(cur.r);
      continue;
    }
    if (stStack.c >= n) ans.push_back(stStack.sol);
    else {
      short t = cur.r;
      if (t < n) st = push(State2(t+1, false)); // immutable
      stStack.plus(t);
      if (valid(stStack.sol)) {
        st = push(State2(t, true)); // immutable
        st = push(onefalse); // immutable
      }
      else stStack.minus(t); // mutable
    }
  }
}
void queensStateRW(int n) {
    ans.clear();
    st = stack<State2>();
    stStack = State(0, vector<int>());
    queensStateR(ans, n);
}

void queensStackR(vector<vector<int> > &ans, int n) {
  st.push(State2(1, false));
  while (!st.empty()) {
    State2 cur = st.top(); st.pop(); // mutable
    if (cur.isminus) {
      stStack.minus(cur.r);
      continue;
    }
    if (stStack.c >= n) ans.push_back(stStack.sol);
    else {
      short t = cur.r;
      if (t < n) st.push(State2(t+1, false)); // mutable
      stStack.plus(t);
      if (valid(stStack.sol)) {
        st.push(State2(t, true)); // mutable
        st.push(onefalse); // mutable
      }
      else stStack.minus(t); // mutable
    }
  }
}
void queensStackRW(int n) {
    ans.clear();
    st = stack<State2>();
    stStack = State(0, vector<int>());
    queensStackR(ans, n);
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

void test (void (*f)(int), string s, int n) {
  int testnum = 6;
  auto t1 = high_resolution_clock::now();

  for (int t = 1; t <= testnum; t ++) {
    f(n);
  }

  auto t2 = high_resolution_clock::now();
  duration<double, milli> ms_double = t2 - t1;
  printf("%s %d %lf\n", s.c_str(), (int) ans.size(), (ms_double.count() / 1000) / testnum);
}

int main() {
  int n = 11;
  // cin >> n;

  test(queensLocalW, "queensLocal", n);
  test(queensGlobalW, "queensGlobal", n);
  test(queensModifyW, "queensModify", n);
  test(queensStateW, "queensState", n);
  test(queensStateRW, "queensStateR", n);
  test(queensStackRW, "queensStackR", n);

  // queensGlobal(ans, 4);
  ans.clear();
  queensStackR(ans, 4);
  st = stack<State2>();
  stStack = State(0, vector<int>());
  for (auto v : ans) print(v);
}

/*
n=10:
queensLocal 724 1.270870
queensGlobal 724 1.196739
queensModify 724 1.141731
queensState 724 1.327756
queensStateR 724 1.289978
queensStackR 724 1.136465 (sometimes slower than queensModify)


n=11:
queensLocal 2680 7.872707
queensGlobal 2680 7.607353
queensModify 2680 7.258673
queensState 2680 8.204634
queensStateR 2680 7.933977
queensStackR 2680 7.224523 (sometimes slower than queensModify)
*/


