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
    auto tmp = stGlobal;
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
    stModify.minus(r);
  }
}

stack<State> st;
void queensStackR(vector<vector<int> > &ans, int n) {
  st.push((State) {0, vector<int>()});
  while (!st.empty()) {
    State cur = st.top(); st.pop();
    if (cur.c >= n) ans.push_back(cur.sol);
    // else for (int r = 1; r <= n; r++) {
    else for (int r = n; r >= 1; r--) {
      cur.plus(r);
      if (valid(cur.sol)) {
        st.push(cur);
      }
      cur.minus(r);
    }
  }
}

// ------------------------------------------------------------------------------
int testnum = 5;

void test1(int n) {
  auto t1 = high_resolution_clock::now();

  for (int t = 1; t <= testnum; t ++) {
    ans.clear();
    queensLocal(ans, n, (State){0, vector<int>()});
  }

  auto t2 = high_resolution_clock::now();
  duration<double, milli> ms_double = t2 - t1;
  printf("queensLocal %d %lf\n", (int) ans.size(), (ms_double.count() / 1000) / testnum);
}

void test2(int n) {
  auto t1 = high_resolution_clock::now();

  for (int t = 1; t <= testnum; t ++) {
    ans.clear();
    stGlobal = (State){0, vector<int>()};
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
    stModify = (State){0, vector<int>()};
    queensModify(ans, n);
  }

  auto t2 = high_resolution_clock::now();
  duration<double, milli> ms_double = t2 - t1;
  printf("queensModify %d %lf\n", (int) ans.size(), (ms_double.count() / 1000) / testnum);
}

void test5(int n) {
  auto t1 = high_resolution_clock::now();

  for (int t = 1; t <= testnum; t ++) {
    ans.clear();
    st = stack<State>();
    queensStackR(ans, n);
  }

  auto t2 = high_resolution_clock::now();
  duration<double, milli> ms_double = t2 - t1;
  printf("queensStackR %d %lf\n", (int) ans.size(), (ms_double.count() / 1000) / testnum);
}



int main() {
  int n = 10;
  // cin >> n;
  test1(n);
  test2(n);
  test3(n);
  test5(n);
  // for (auto v : ans) print(v);
}

/*
queensLocal 724 1.274214
queensGlobal 724 1.191334
queensModify 724 1.150410
queensStackR 724 1.152278
*/


