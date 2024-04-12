#ifndef ATCODER_LIBRARY
#define ATCODER_LIBRARY
#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <limits>
#include <numeric>
#include <queue>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>
#ifdef _MSC_VER
#include <intrin.h>
#endif
namespace atcoder{
using namespace std;
template<class T> using V=vector<T>;
using i64=long long;
using u64=unsigned long long;
using u32=unsigned int;
namespace internal{
int ceil_pow2(int n){
int x = 0;
while((1U << x)<(u32)(n))x++;
return x;
}
int bsf(u32 n){
#ifdef _MSC_VER
unsigned long index;
_BitScanForward(&index,n);
return index;
#else
return __builtin_ctz(n);
#endif
}
constexpr i64 safe_mod(i64 x,i64 m){
x%= m;
if(x < 0)x+= m;
return x;
}
struct barrett{
u32 _m;
u64 im;
barrett(u32 m): _m(m),im((u64)(-1)/m+1){}
u32 umod()const{return _m;}
u32 mul(u32 a,u32 b)const{
u64 z = a;
z *= b;
#ifdef _MSC_VER
u64 x;
_umul128(z,im,&x);
#else
u64 x =
(u64)(((unsigned __int128)(z)*im)>> 64);
#endif
u32 v =(u32)(z-x * _m);
if(_m <= v)v+= _m;
return v;
}
};
constexpr i64 pow_mod_constexpr(i64 x,i64 n,int m){
if(m == 1)return 0;
u32 _m =(u32)(m);
u64 r = 1;
u64 y = safe_mod(x,m);
while(n){
if(n & 1)r =(r * y)%_m;
y =(y * y)%_m;
n >>= 1;
}
return r;
}
constexpr bool is_prime_constexpr(int n){
if(n <= 1)return false;
if(n == 2 || n == 7 || n == 61)return true;
if(n%2 == 0)return false;
i64 d = n-1;
while(d%2 == 0)d/= 2;
for(i64 a :{2,7,61}){
i64 t = d;
i64 y = pow_mod_constexpr(a,t,n);
while(t != n-1 && y != 1 && y != n-1){
y = y * y%n;
t <<= 1;
}
if(y != n-1 && t%2 == 0){
return false;
}
}
return true;
}
template <int n> constexpr bool is_prime = is_prime_constexpr(n);
constexpr pair<i64,i64> inv_gcd(i64 a,i64 b){
a = safe_mod(a,b);
if(a == 0)return{b,0};
i64 s = b,t = a;
i64 m0 = 0,m1 = 1;
while(t){
i64 u = s/t;
s-= t * u;
m0-= m1 * u;
auto tmp = s;
s = t;
t = tmp;
tmp = m0;
m0 = m1;
m1 = tmp;
}
if(m0 < 0)m0+= b/s;
return{s,m0};
}
constexpr int primitive_root_constexpr(int m){
if(m == 2)return 1;
if(m == 167772161)return 3;
if(m == 469762049)return 3;
if(m == 754974721)return 11;
if(m == 998244353)return 3;
int divs[20] ={};
divs[0] = 2;
int cnt = 1;
int x =(m-1)/2;
while(x%2 == 0)x/= 2;
for(int i = 3;(i64)(i)*i <= x; i+= 2){
if(x%i == 0){
divs[cnt++] = i;
while(x%i == 0){
x/= i;
}
}
}
if(x > 1){
divs[cnt++] = x;
}
for(int g = 2;; g++){
bool ok = true;
for(int i = 0; i < cnt; i++){
if(pow_mod_constexpr(g,(m-1)/divs[i],m)== 1){
ok = false;
break;
}
}
if(ok)return g;
}
}
template <int m> constexpr int primitive_root = primitive_root_constexpr(m);
template <class T> struct simple_queue{
V<T> payload;
int pos = 0;
void reserve(int n){payload.reserve(n);}
int size()const{return int(payload.size())-pos;}
bool empty()const{return pos == int(payload.size());}
void push(const T& t){payload.push_back(t);}
T& front(){return payload[pos];}
void clear(){
payload.clear();
pos = 0;
}
void pop(){pos++;}
};
template <class E> struct csr{
V<int> start;
V<E> elist;
csr(int n,const V<pair<int,E>>& edges)
: start(n+1),elist(edges.size()){
for(auto e : edges){
start[e.first+1]++;
}
for(int i = 1; i <= n; i++){
start[i]+= start[i-1];
}
auto counter = start;
for(auto e : edges){
elist[counter[e.first]++] = e.second;
}
}
};
struct scc_graph{
public:
scc_graph(int n): _n(n){}
int num_vertices(){return _n;}
void add_edge(int from,int to){edges.push_back({from,{to}});}
pair<int,V<int>> scc_ids(){
auto g = csr<edge>(_n,edges);
int now_ord = 0,group_num = 0;
V<int> visited,low(_n),ord(_n,-1),ids(_n);
visited.reserve(_n);
auto dfs = [&](auto self,int v)-> void{
low[v] = ord[v] = now_ord++;
visited.push_back(v);
for(int i = g.start[v]; i < g.start[v+1]; i++){
auto to = g.elist[i].to;
if(ord[to] ==-1){
self(self,to);
low[v] = min(low[v],low[to]);
}else{
low[v] = min(low[v],ord[to]);
}
}
if(low[v] == ord[v]){
while(true){
int u = visited.back();
visited.pop_back();
ord[u] = _n;
ids[u] = group_num;
if(u == v)break;
}
group_num++;
}
};
for(int i = 0; i < _n; i++){
if(ord[i] ==-1)dfs(dfs,i);
}
for(auto& x : ids){
x = group_num-1-x;
}
return{group_num,ids};
}
V<V<int>> scc(){
auto ids = scc_ids();
int group_num = ids.first;
V<int> counts(group_num);
for(auto x : ids.second)counts[x]++;
V<V<int>> groups(ids.first);
for(int i = 0; i < group_num; i++){
groups[i].reserve(counts[i]);
}
for(int i = 0; i < _n; i++){
groups[ids.second[i]].push_back(i);
}
return groups;
}
private:
int _n;
struct edge{
int to;
};
V<pair<int,edge>> edges;
};
#ifndef _MSC_VER
template <class T>
using is_signed_int128 =
typename std::conditional<is_same<T,__int128_t>::value ||
is_same<T,__int128>::value,
true_type,
false_type>::type;
template <class T>
using is_unsigned_int128 =
typename std::conditional<is_same<T,__uint128_t>::value ||
is_same<T,unsigned __int128>::value,
true_type,
false_type>::type;
template <class T>
using make_unsigned_int128 =
typename std::conditional<is_same<T,__int128_t>::value,
__uint128_t,
unsigned __int128>;
template <class T>
using is_integral = typename std::conditional<is_integral<T>::value ||
is_signed_int128<T>::value ||
is_unsigned_int128<T>::value,
true_type,
false_type>::type;
template <class T>
using is_signed_int = typename std::conditional<(is_integral<T>::value &&
is_signed<T>::value)||
is_signed_int128<T>::value,
true_type,
false_type>::type;
template <class T>
using is_unsigned_int =
typename std::conditional<(is_integral<T>::value &&
is_unsigned<T>::value)||
is_unsigned_int128<T>::value,
true_type,
false_type>::type;
template <class T>
using to_unsigned = typename std::conditional<
is_signed_int128<T>::value,
make_unsigned_int128<T>,
typename std::conditional<is_signed<T>::value,
make_unsigned<T>,
common_type<T>>::type>::type;
#else
template <class T> using is_integral = typename is_integral<T>;
template <class T>
using is_signed_int =
typename std::conditional<is_integral<T>::value && is_signed<T>::value,
true_type,
false_type>::type;
template <class T>
using is_unsigned_int =
typename std::conditional<is_integral<T>::value &&
is_unsigned<T>::value,
true_type,
false_type>::type;
template <class T>
using to_unsigned = typename std::conditional<is_signed_int<T>::value,
make_unsigned<T>,
common_type<T>>::type;
#endif
template <class T>
using is_signed_int_t = enable_if_t<is_signed_int<T>::value>;
template <class T>
using is_unsigned_int_t = enable_if_t<is_unsigned_int<T>::value>;
template <class T> using to_unsigned_t = typename to_unsigned<T>::type;
struct modint_base{};
struct static_modint_base : modint_base{};
template <class T> using is_modint = is_base_of<modint_base,T>;
template <class T> using is_modint_t = enable_if_t<is_modint<T>::value>;
}
template <int m,enable_if_t<(1 <= m)>* = nullptr>
struct static_modint : internal::static_modint_base{
using mint = static_modint;
public:
static constexpr int mod(){return m;}
static mint raw(int v){
mint x;
x._v = v;
return x;
}
static_modint(): _v(0){}
template <class T,internal::is_signed_int_t<T>* = nullptr>
static_modint(T v){
i64 x =(i64)(v%(i64)(umod()));
if(x < 0)x+= umod();
_v =(u32)(x);
}
template <class T,internal::is_unsigned_int_t<T>* = nullptr>
static_modint(T v){
_v =(u32)(v%umod());
}
static_modint(bool v){_v =((u32)(v)%umod());}
u32 val()const{return _v;}
mint& operator++(){
_v++;
if(_v == umod())_v = 0;
return *this;
}
mint& operator--(){
if(_v == 0)_v = umod();
_v--;
return *this;
}
mint operator++(int){
mint result = *this;
++*this;
return result;
}
mint operator--(int){
mint result = *this;
--*this;
return result;
}
mint& operator+=(const mint& rhs){
_v+= rhs._v;
if(_v >= umod())_v-= umod();
return *this;
}
mint& operator-=(const mint& rhs){
_v-= rhs._v;
if(_v >= umod())_v+= umod();
return *this;
}
mint& operator*=(const mint& rhs){
u64 z = _v;
z *= rhs._v;
_v =(u32)(z%umod());
return *this;
}
mint& operator/=(const mint& rhs){return *this = *this * rhs.inv();}
mint operator+()const{return *this;}
mint operator-()const{return mint()-*this;}
mint pow(i64 n)const{
assert(0 <= n);
mint x = *this,r = 1;
while(n){
if(n & 1)r *= x;
x *= x;
n >>= 1;
}
return r;
}
mint inv()const{
if(prime){
assert(_v);
return pow(umod()-2);
}else{
auto eg = internal::inv_gcd(_v,m);
assert(eg.first == 1);
return eg.second;
}
}
friend mint operator+(const mint& lhs,const mint& rhs){
return mint(lhs)+= rhs;
}
friend mint operator-(const mint& lhs,const mint& rhs){
return mint(lhs)-= rhs;
}
friend mint operator*(const mint& lhs,const mint& rhs){
return mint(lhs)*= rhs;
}
friend mint operator/(const mint& lhs,const mint& rhs){
return mint(lhs)/= rhs;
}
friend bool operator==(const mint& lhs,const mint& rhs){
return lhs._v == rhs._v;
}
friend bool operator!=(const mint& lhs,const mint& rhs){
return lhs._v != rhs._v;
}
private:
u32 _v;
static constexpr u32 umod(){return m;}
static constexpr bool prime = internal::is_prime<m>;
};
template <int id> struct dynamic_modint : internal::modint_base{
using mint = dynamic_modint;
public:
static int mod(){return(int)(bt.umod());}
static void set_mod(int m){
assert(1 <= m);
bt = internal::barrett(m);
}
static mint raw(int v){
mint x;
x._v = v;
return x;
}
dynamic_modint(): _v(0){}
template <class T,internal::is_signed_int_t<T>* = nullptr>
dynamic_modint(T v){
i64 x =(i64)(v%(i64)(mod()));
if(x < 0)x+= mod();
_v =(u32)(x);
}
template <class T,internal::is_unsigned_int_t<T>* = nullptr>
dynamic_modint(T v){
_v =(u32)(v%mod());
}
dynamic_modint(bool v){_v =((u32)(v)%mod());}
u32 val()const{return _v;}
mint& operator++(){
_v++;
if(_v == umod())_v = 0;
return *this;
}
mint& operator--(){
if(_v == 0)_v = umod();
_v--;
return *this;
}
mint operator++(int){
mint result = *this;
++*this;
return result;
}
mint operator--(int){
mint result = *this;
--*this;
return result;
}
mint& operator+=(const mint& rhs){
_v+= rhs._v;
if(_v >= umod())_v-= umod();
return *this;
}
mint& operator-=(const mint& rhs){
_v+= mod()-rhs._v;
if(_v >= umod())_v-= umod();
return *this;
}
mint& operator*=(const mint& rhs){
_v = bt.mul(_v,rhs._v);
return *this;
}
mint& operator/=(const mint& rhs){return *this = *this * rhs.inv();}
mint operator+()const{return *this;}
mint operator-()const{return mint()-*this;}
mint pow(i64 n)const{
assert(0 <= n);
mint x = *this,r = 1;
while(n){
if(n & 1)r *= x;
x *= x;
n >>= 1;
}
return r;
}
mint inv()const{
auto eg = internal::inv_gcd(_v,mod());
assert(eg.first == 1);
return eg.second;
}
friend mint operator+(const mint& lhs,const mint& rhs){
return mint(lhs)+= rhs;
}
friend mint operator-(const mint& lhs,const mint& rhs){
return mint(lhs)-= rhs;
}
friend mint operator*(const mint& lhs,const mint& rhs){
return mint(lhs)*= rhs;
}
friend mint operator/(const mint& lhs,const mint& rhs){
return mint(lhs)/= rhs;
}
friend bool operator==(const mint& lhs,const mint& rhs){
return lhs._v == rhs._v;
}
friend bool operator!=(const mint& lhs,const mint& rhs){
return lhs._v != rhs._v;
}
private:
u32 _v;
static internal::barrett bt;
static u32 umod(){return bt.umod();}
};
template <int id> internal::barrett dynamic_modint<id>::bt = 998244353;
using modint998244353 = static_modint<998244353>;
using modint1000000007 = static_modint<1000000007>;
using modint = dynamic_modint<-1>;
namespace internal{
template <class T>
using is_static_modint = is_base_of<internal::static_modint_base,T>;
template <class T>
using is_static_modint_t = enable_if_t<is_static_modint<T>::value>;
template <class> struct is_dynamic_modint : public false_type{};
template <int id>
struct is_dynamic_modint<dynamic_modint<id>> : public true_type{};
template <class T>
using is_dynamic_modint_t = enable_if_t<is_dynamic_modint<T>::value>;
template <class mint,internal::is_static_modint_t<mint>* = nullptr>
void butterfly(V<mint>& a){
static constexpr int g = internal::primitive_root<mint::mod()>;
int n = int(a.size());
int h = internal::ceil_pow2(n);
static bool first = true;
static mint sum_e[30];
if(first){
first = false;
mint es[30],ies[30];
int cnt2 = bsf(mint::mod()-1);
mint e = mint(g).pow((mint::mod()-1)>> cnt2),ie = e.inv();
for(int i = cnt2; i >= 2; i--){
es[i-2] = e;
ies[i-2] = ie;
e *= e;
ie *= ie;
}
mint now = 1;
for(int i = 0; i < cnt2-2; i++){
sum_e[i] = es[i] * now;
now *= ies[i];
}
}
for(int ph = 1; ph <= h; ph++){
int w = 1 <<(ph-1),p = 1 <<(h-ph);
mint now = 1;
for(int s = 0; s < w; s++){
int j = s <<(h-ph+1);
for(int i = 0; i < p; i++){
auto l = a[i+j];
auto r = a[i+j+p] * now;
a[i+j] = l+r;
a[i+j+p] = l-r;
}
now *= sum_e[bsf(~(u32)(s))];
}
}
}
template <class mint,internal::is_static_modint_t<mint>* = nullptr>
void butterfly_inv(V<mint>& a){
static constexpr int g = internal::primitive_root<mint::mod()>;
int n = int(a.size());
int h = internal::ceil_pow2(n);
static bool first = true;
static mint sum_ie[30];
if(first){
first = false;
mint es[30],ies[30];
int cnt2 = bsf(mint::mod()-1);
mint e = mint(g).pow((mint::mod()-1)>> cnt2),ie = e.inv();
for(int i = cnt2; i >= 2; i--){
es[i-2] = e;
ies[i-2] = ie;
e *= e;
ie *= ie;
}
mint now = 1;
for(int i = 0; i < cnt2-2; i++){
sum_ie[i] = ies[i] * now;
now *= es[i];
}
}
for(int ph = h; ph >= 1; ph--){
int w = 1 <<(ph-1),p = 1 <<(h-ph);
mint inow = 1;
for(int s = 0; s < w; s++){
int j = s <<(h-ph+1);
for(int i = 0; i < p; i++){
auto l = a[i+j];
auto r = a[i+j+p];
a[i+j] = l+r;
a[i+j+p] =
(u64)(mint::mod()+l.val()-r.val())*
inow.val();
}
inow *= sum_ie[bsf(~(u32)(s))];
}
}
}
}
template <class mint,internal::is_static_modint_t<mint>* = nullptr>
V<mint> convolution(V<mint> a,V<mint> b){
int n = int(a.size()),m = int(b.size());
if(!n || !m)return{};
if(min(n,m)<= 60){
if(n < m){
swap(n,m);
swap(a,b);
}
V<mint> ans(n+m-1);
for(int i = 0; i < n; i++){
for(int j = 0; j < m; j++){
ans[i+j]+= a[i] * b[j];
}
}
return ans;
}
int z = 1 << internal::ceil_pow2(n+m-1);
a.resize(z);
internal::butterfly(a);
b.resize(z);
internal::butterfly(b);
for(int i = 0; i < z; i++){
a[i] *= b[i];
}
internal::butterfly_inv(a);
a.resize(n+m-1);
mint iz = mint(z).inv();
for(int i = 0; i < n+m-1; i++)a[i] *= iz;
return a;
}
template <u32 mod = 998244353,
class T,
enable_if_t<internal::is_integral<T>::value>* = nullptr>
V<T> convolution(const V<T>& a,const V<T>& b){
int n = int(a.size()),m = int(b.size());
if(!n || !m)return{};
using mint = static_modint<mod>;
V<mint> a2(n),b2(m);
for(int i = 0; i < n; i++){
a2[i] = mint(a[i]);
}
for(int i = 0; i < m; i++){
b2[i] = mint(b[i]);
}
auto c2 = convolution(move(a2),move(b2));
V<T> c(n+m-1);
for(int i = 0; i < n+m-1; i++){
c[i] = c2[i].val();
}
return c;
}
V<i64> convolution_ll(const V<i64>& a,
const V<i64>& b){
int n = int(a.size()),m = int(b.size());
if(!n || !m)return{};
static constexpr u64 MOD1 = 754974721;
static constexpr u64 MOD2 = 167772161;
static constexpr u64 MOD3 = 469762049;
static constexpr u64 M2M3 = MOD2 * MOD3;
static constexpr u64 M1M3 = MOD1 * MOD3;
static constexpr u64 M1M2 = MOD1 * MOD2;
static constexpr u64 M1M2M3 = MOD1 * MOD2 * MOD3;
static constexpr u64 i1 =
internal::inv_gcd(MOD2 * MOD3,MOD1).second;
static constexpr u64 i2 =
internal::inv_gcd(MOD1 * MOD3,MOD2).second;
static constexpr u64 i3 =
internal::inv_gcd(MOD1 * MOD2,MOD3).second;
auto c1 = convolution<MOD1>(a,b);
auto c2 = convolution<MOD2>(a,b);
auto c3 = convolution<MOD3>(a,b);
V<i64> c(n+m-1);
for(int i = 0; i < n+m-1; i++){
u64 x = 0;
x+=(c1[i] * i1)%MOD1 * M2M3;
x+=(c2[i] * i2)%MOD2 * M1M3;
x+=(c3[i] * i3)%MOD3 * M1M2;
i64 diff =
c1[i]-internal::safe_mod((i64)(x),(i64)(MOD1));
if(diff < 0)diff+= MOD1;
static constexpr u64 j[5] ={
0,0,M1M2M3,2 * M1M2M3,3 * M1M2M3};
x-= j[diff%5];
c[i] = x;
}
return c;
}
struct dsu{
public:
dsu(): _n(0){}
dsu(int n): _n(n),parent_or_size(n,-1){}
int merge(int a,int b){
assert(0 <= a && a < _n);
assert(0 <= b && b < _n);
int x = leader(a),y = leader(b);
if(x == y)return x;
if(-parent_or_size[x] <-parent_or_size[y])swap(x,y);
parent_or_size[x]+= parent_or_size[y];
parent_or_size[y] = x;
return x;
}
bool same(int a,int b){
assert(0 <= a && a < _n);
assert(0 <= b && b < _n);
return leader(a)== leader(b);
}
int leader(int a){
assert(0 <= a && a < _n);
if(parent_or_size[a] < 0)return a;
return parent_or_size[a] = leader(parent_or_size[a]);
}
int size(int a){
assert(0 <= a && a < _n);
return-parent_or_size[leader(a)];
}
V<V<int>> groups(){
V<int> leader_buf(_n),group_size(_n);
for(int i = 0; i < _n; i++){
leader_buf[i] = leader(i);
group_size[leader_buf[i]]++;
}
V<V<int>> result(_n);
for(int i = 0; i < _n; i++){
result[i].reserve(group_size[i]);
}
for(int i = 0; i < _n; i++){
result[leader_buf[i]].push_back(i);
}
result.erase(
remove_if(result.begin(),result.end(),
[&](const V<int>& v){return v.empty();}),
result.end());
return result;
}
private:
int _n;
V<int> parent_or_size;
};
template <class T> struct fenwick_tree{
using U = internal::to_unsigned_t<T>;
public:
fenwick_tree(): _n(0){}
fenwick_tree(int n): _n(n),data(n){}
void add(int p,T x){
assert(0 <= p && p < _n);
p++;
while(p <= _n){
data[p-1]+= U(x);
p+= p &-p;
}
}
T sum(int l,int r){
assert(0 <= l && l <= r && r <= _n);
return sum(r)-sum(l);
}
private:
int _n;
V<U> data;
U sum(int r){
U s = 0;
while(r > 0){
s+= data[r-1];
r-= r &-r;
}
return s;
}
};
template <class S,
S(*op)(S,S),
S(*e)(),
class F,
S(*mapping)(F,S),
F(*composition)(F,F),
F(*id)()>
struct lazy_segtree{
public:
lazy_segtree(): lazy_segtree(0){}
lazy_segtree(int n): lazy_segtree(V<S>(n,e())){}
lazy_segtree(const V<S>& v): _n(int(v.size())){
log = internal::ceil_pow2(_n);
size = 1 << log;
d = V<S>(2 * size,e());
lz = V<F>(size,id());
for(int i = 0; i < _n; i++)d[size+i] = v[i];
for(int i = size-1; i >= 1; i--){
update(i);
}
}
void set(int p,S x){
assert(0 <= p && p < _n);
p+= size;
for(int i = log; i >= 1; i--)push(p >> i);
d[p] = x;
for(int i = 1; i <= log; i++)update(p >> i);
}
S get(int p){
assert(0 <= p && p < _n);
p+= size;
for(int i = log; i >= 1; i--)push(p >> i);
return d[p];
}
S prod(int l,int r){
assert(0 <= l && l <= r && r <= _n);
if(l == r)return e();
l+= size;
r+= size;
for(int i = log; i >= 1; i--){
if(((l >> i)<< i)!= l)push(l >> i);
if(((r >> i)<< i)!= r)push(r >> i);
}
S sml = e(),smr = e();
while(l < r){
if(l & 1)sml = op(sml,d[l++]);
if(r & 1)smr = op(d[--r],smr);
l >>= 1;
r >>= 1;
}
return op(sml,smr);
}
S all_prod(){return d[1];}
void apply(int p,F f){
assert(0 <= p && p < _n);
p+= size;
for(int i = log; i >= 1; i--)push(p >> i);
d[p] = mapping(f,d[p]);
for(int i = 1; i <= log; i++)update(p >> i);
}
void apply(int l,int r,F f){
assert(0 <= l && l <= r && r <= _n);
if(l == r)return;
l+= size;
r+= size;
for(int i = log; i >= 1; i--){
if(((l >> i)<< i)!= l)push(l >> i);
if(((r >> i)<< i)!= r)push((r-1)>> i);
}
{
int l2 = l,r2 = r;
while(l < r){
if(l & 1)all_apply(l++,f);
if(r & 1)all_apply(--r,f);
l >>= 1;
r >>= 1;
}
l = l2;
r = r2;
}
for(int i = 1; i <= log; i++){
if(((l >> i)<< i)!= l)update(l >> i);
if(((r >> i)<< i)!= r)update((r-1)>> i);
}
}
template <bool(*g)(S)> int max_right(int l){
return max_right(l,[](S x){return g(x);});
}
template <class G> int max_right(int l,G g){
assert(0 <= l && l <= _n);
assert(g(e()));
if(l == _n)return _n;
l+= size;
for(int i = log; i >= 1; i--)push(l >> i);
S sm = e();
do{
while(l%2 == 0)l >>= 1;
if(!g(op(sm,d[l]))){
while(l < size){
push(l);
l =(2 * l);
if(g(op(sm,d[l]))){
sm = op(sm,d[l]);
l++;
}
}
return l-size;
}
sm = op(sm,d[l]);
l++;
}while((l &-l)!= l);
return _n;
}
template <bool(*g)(S)> int min_left(int r){
return min_left(r,[](S x){return g(x);});
}
template <class G> int min_left(int r,G g){
assert(0 <= r && r <= _n);
assert(g(e()));
if(r == 0)return 0;
r+= size;
for(int i = log; i >= 1; i--)push((r-1)>> i);
S sm = e();
do{
r--;
while(r > 1 &&(r%2))r >>= 1;
if(!g(op(d[r],sm))){
while(r < size){
push(r);
r =(2 * r+1);
if(g(op(d[r],sm))){
sm = op(d[r],sm);
r--;
}
}
return r+1-size;
}
sm = op(d[r],sm);
}while((r &-r)!= r);
return 0;
}
private:
int _n,size,log;
V<S> d;
V<F> lz;
void update(int k){d[k] = op(d[2 * k],d[2 * k+1]);}
void all_apply(int k,F f){
d[k] = mapping(f,d[k]);
if(k < size)lz[k] = composition(f,lz[k]);
}
void push(int k){
all_apply(2 * k,lz[k]);
all_apply(2 * k+1,lz[k]);
lz[k] = id();
}
};
i64 pow_mod(i64 x,i64 n,int m){
assert(0 <= n && 1 <= m);
if(m == 1)return 0;
internal::barrett bt((u32)(m));
u32 r = 1,y =(u32)(internal::safe_mod(x,m));
while(n){
if(n & 1)r = bt.mul(r,y);
y = bt.mul(y,y);
n >>= 1;
}
return r;
}
i64 inv_mod(i64 x,i64 m){
assert(1 <= m);
auto z = internal::inv_gcd(x,m);
assert(z.first == 1);
return z.second;
}
pair<i64,i64> crt(const V<i64>& r,
const V<i64>& m){
assert(r.size()== m.size());
int n = int(r.size());
i64 r0 = 0,m0 = 1;
for(int i = 0; i < n; i++){
assert(1 <= m[i]);
i64 r1 = internal::safe_mod(r[i],m[i]),m1 = m[i];
if(m0 < m1){
swap(r0,r1);
swap(m0,m1);
}
if(m0%m1 == 0){
if(r0%m1 != r1)return{0,0};
continue;
}
i64 g,im;
tie(g,im)= internal::inv_gcd(m0,m1);
i64 u1 =(m1/g);
if((r1-r0)%g)return{0,0};
i64 x =(r1-r0)/g%u1 * im%u1;
r0+= x * m0;
m0 *= u1;
if(r0 < 0)r0+= m0;
}
return{r0,m0};
}
i64 floor_sum(i64 n,i64 m,i64 a,i64 b){
i64 ans = 0;
if(a >= m){
ans+=(n-1)* n *(a/m)/2;
a%= m;
}
if(b >= m){
ans+= n *(b/m);
b%= m;
}
i64 y_max =(a * n+b)/m,x_max =(y_max * m-b);
if(y_max == 0)return ans;
ans+=(n-(x_max+a-1)/a)* y_max;
ans+= floor_sum(y_max,a,m,(a-x_max%a)%a);
return ans;
}
template <class Cap> struct mf_graph{
public:
mf_graph(): _n(0){}
mf_graph(int n): _n(n),g(n){}
int add_edge(int from,int to,Cap cap){
assert(0 <= from && from < _n);
assert(0 <= to && to < _n);
assert(0 <= cap);
int m = int(pos.size());
pos.push_back({from,int(g[from].size())});
g[from].push_back(_edge{to,int(g[to].size()),cap});
g[to].push_back(_edge{from,int(g[from].size())-1,0});
return m;
}
struct edge{
int from,to;
Cap cap,flow;
};
edge get_edge(int i){
int m = int(pos.size());
assert(0 <= i && i < m);
auto _e = g[pos[i].first][pos[i].second];
auto _re = g[_e.to][_e.rev];
return edge{pos[i].first,_e.to,_e.cap+_re.cap,_re.cap};
}
V<edge> edges(){
int m = int(pos.size());
V<edge> result;
for(int i = 0; i < m; i++){
result.push_back(get_edge(i));
}
return result;
}
void change_edge(int i,Cap new_cap,Cap new_flow){
int m = int(pos.size());
assert(0 <= i && i < m);
assert(0 <= new_flow && new_flow <= new_cap);
auto& _e = g[pos[i].first][pos[i].second];
auto& _re = g[_e.to][_e.rev];
_e.cap = new_cap-new_flow;
_re.cap = new_flow;
}
Cap flow(int s,int t){
return flow(s,t,numeric_limits<Cap>::max());
}
Cap flow(int s,int t,Cap flow_limit){
assert(0 <= s && s < _n);
assert(0 <= t && t < _n);
V<int> level(_n),iter(_n);
internal::simple_queue<int> que;
auto bfs = [&](){
fill(level.begin(),level.end(),-1);
level[s] = 0;
que.clear();
que.push(s);
while(!que.empty()){
int v = que.front();
que.pop();
for(auto e : g[v]){
if(e.cap == 0 || level[e.to] >= 0)continue;
level[e.to] = level[v]+1;
if(e.to == t)return;
que.push(e.to);
}
}
};
auto dfs = [&](auto self,int v,Cap up){
if(v == s)return up;
Cap res = 0;
int level_v = level[v];
for(int& i = iter[v]; i < int(g[v].size()); i++){
_edge& e = g[v][i];
if(level_v <= level[e.to] || g[e.to][e.rev].cap == 0)continue;
Cap d =
self(self,e.to,min(up-res,g[e.to][e.rev].cap));
if(d <= 0)continue;
g[v][i].cap+= d;
g[e.to][e.rev].cap-= d;
res+= d;
if(res == up)break;
}
return res;
};
Cap flow = 0;
while(flow < flow_limit){
bfs();
if(level[t] ==-1)break;
fill(iter.begin(),iter.end(),0);
while(flow < flow_limit){
Cap f = dfs(dfs,t,flow_limit-flow);
if(!f)break;
flow+= f;
}
}
return flow;
}
V<bool> min_cut(int s){
V<bool> visited(_n);
internal::simple_queue<int> que;
que.push(s);
while(!que.empty()){
int p = que.front();
que.pop();
visited[p] = true;
for(auto e : g[p]){
if(e.cap && !visited[e.to]){
visited[e.to] = true;
que.push(e.to);
}
}
}
return visited;
}
private:
int _n;
struct _edge{
int to,rev;
Cap cap;
};
V<pair<int,int>> pos;
V<V<_edge>> g;
};
template <class Cap,class Cost> struct mcf_graph{
public:
mcf_graph(){}
mcf_graph(int n): _n(n),g(n){}
int add_edge(int from,int to,Cap cap,Cost cost){
assert(0 <= from && from < _n);
assert(0 <= to && to < _n);
int m = int(pos.size());
pos.push_back({from,int(g[from].size())});
g[from].push_back(_edge{to,int(g[to].size()),cap,cost});
g[to].push_back(_edge{from,int(g[from].size())-1,0,-cost});
return m;
}
struct edge{
int from,to;
Cap cap,flow;
Cost cost;
};
edge get_edge(int i){
int m = int(pos.size());
assert(0 <= i && i < m);
auto _e = g[pos[i].first][pos[i].second];
auto _re = g[_e.to][_e.rev];
return edge{
pos[i].first,_e.to,_e.cap+_re.cap,_re.cap,_e.cost,
};
}
V<edge> edges(){
int m = int(pos.size());
V<edge> result(m);
for(int i = 0; i < m; i++){
result[i] = get_edge(i);
}
return result;
}
pair<Cap,Cost> flow(int s,int t){
return flow(s,t,numeric_limits<Cap>::max());
}
pair<Cap,Cost> flow(int s,int t,Cap flow_limit){
return slope(s,t,flow_limit).back();
}
V<pair<Cap,Cost>> slope(int s,int t){
return slope(s,t,numeric_limits<Cap>::max());
}
V<pair<Cap,Cost>> slope(int s,int t,Cap flow_limit){
assert(0 <= s && s < _n);
assert(0 <= t && t < _n);
assert(s != t);
V<Cost> dual(_n,0),dist(_n);
V<int> pv(_n),pe(_n);
V<bool> vis(_n);
auto dual_ref = [&](){
fill(dist.begin(),dist.end(),
numeric_limits<Cost>::max());
fill(pv.begin(),pv.end(),-1);
fill(pe.begin(),pe.end(),-1);
fill(vis.begin(),vis.end(),false);
struct Q{
Cost key;
int to;
bool operator<(Q r)const{return key > r.key;}
};
priority_queue<Q> que;
dist[s] = 0;
que.push(Q{0,s});
while(!que.empty()){
int v = que.top().to;
que.pop();
if(vis[v])continue;
vis[v] = true;
if(v == t)break;
for(int i = 0; i < int(g[v].size()); i++){
auto e = g[v][i];
if(vis[e.to] || !e.cap)continue;
Cost cost = e.cost-dual[e.to]+dual[v];
if(dist[e.to]-dist[v] > cost){
dist[e.to] = dist[v]+cost;
pv[e.to] = v;
pe[e.to] = i;
que.push(Q{dist[e.to],e.to});
}
}
}
if(!vis[t]){
return false;
}
for(int v = 0; v < _n; v++){
if(!vis[v])continue;
dual[v]-= dist[t]-dist[v];
}
return true;
};
Cap flow = 0;
Cost cost = 0,prev_cost =-1;
V<pair<Cap,Cost>> result;
result.push_back({flow,cost});
while(flow < flow_limit){
if(!dual_ref())break;
Cap c = flow_limit-flow;
for(int v = t; v != s; v = pv[v]){
c = min(c,g[pv[v]][pe[v]].cap);
}
for(int v = t; v != s; v = pv[v]){
auto& e = g[pv[v]][pe[v]];
e.cap-= c;
g[v][e.rev].cap+= c;
}
Cost d =-dual[s];
flow+= c;
cost+= c * d;
if(prev_cost == d){
result.pop_back();
}
result.push_back({flow,cost});
prev_cost = cost;
}
return result;
}
private:
int _n;
struct _edge{
int to,rev;
Cap cap;
Cost cost;
};
V<pair<int,int>> pos;
V<V<_edge>> g;
};
struct scc_graph{
public:
scc_graph(): internal(0){}
scc_graph(int n): internal(n){}
void add_edge(int from,int to){
int n = internal.num_vertices();
assert(0 <= from && from < n);
assert(0 <= to && to < n);
internal.add_edge(from,to);
}
V<V<int>> scc(){return internal.scc();}
private:
internal::scc_graph internal;
};
template <class S,S(*op)(S,S),S(*e)()> struct segtree{
public:
segtree(): segtree(0){}
segtree(int n): segtree(V<S>(n,e())){}
segtree(const V<S>& v): _n(int(v.size())){
log = internal::ceil_pow2(_n);
size = 1 << log;
d = V<S>(2 * size,e());
for(int i = 0; i < _n; i++)d[size+i] = v[i];
for(int i = size-1; i >= 1; i--){
update(i);
}
}
void set(int p,S x){
assert(0 <= p && p < _n);
p+= size;
d[p] = x;
for(int i = 1; i <= log; i++)update(p >> i);
}
S get(int p){
assert(0 <= p && p < _n);
return d[p+size];
}
S prod(int l,int r){
assert(0 <= l && l <= r && r <= _n);
S sml = e(),smr = e();
l+= size;
r+= size;
while(l < r){
if(l & 1)sml = op(sml,d[l++]);
if(r & 1)smr = op(d[--r],smr);
l >>= 1;
r >>= 1;
}
return op(sml,smr);
}
S all_prod(){return d[1];}
template <bool(*f)(S)> int max_right(int l){
return max_right(l,[](S x){return f(x);});
}
template <class F> int max_right(int l,F f){
assert(0 <= l && l <= _n);
assert(f(e()));
if(l == _n)return _n;
l+= size;
S sm = e();
do{
while(l%2 == 0)l >>= 1;
if(!f(op(sm,d[l]))){
while(l < size){
l =(2 * l);
if(f(op(sm,d[l]))){
sm = op(sm,d[l]);
l++;
}
}
return l-size;
}
sm = op(sm,d[l]);
l++;
}while((l &-l)!= l);
return _n;
}
template <bool(*f)(S)> int min_left(int r){
return min_left(r,[](S x){return f(x);});
}
template <class F> int min_left(int r,F f){
assert(0 <= r && r <= _n);
assert(f(e()));
if(r == 0)return 0;
r+= size;
S sm = e();
do{
r--;
while(r > 1 &&(r%2))r >>= 1;
if(!f(op(d[r],sm))){
while(r < size){
r =(2 * r+1);
if(f(op(d[r],sm))){
sm = op(d[r],sm);
r--;
}
}
return r+1-size;
}
sm = op(d[r],sm);
}while((r &-r)!= r);
return 0;
}
private:
int _n,size,log;
V<S> d;
void update(int k){d[k] = op(d[2 * k],d[2 * k+1]);}
};
namespace internal{
V<int> sa_naive(const V<int>& s){
int n = int(s.size());
V<int> sa(n);
iota(sa.begin(),sa.end(),0);
sort(sa.begin(),sa.end(),[&](int l,int r){
if(l == r)return false;
while(l < n && r < n){
if(s[l] != s[r])return s[l] < s[r];
l++;
r++;
}
return l == n;
});
return sa;
}
V<int> sa_doubling(const V<int>& s){
int n = int(s.size());
V<int> sa(n),rnk = s,tmp(n);
iota(sa.begin(),sa.end(),0);
for(int k = 1; k < n; k *= 2){
auto cmp = [&](int x,int y){
if(rnk[x] != rnk[y])return rnk[x] < rnk[y];
int rx = x+k < n ? rnk[x+k] :-1;
int ry = y+k < n ? rnk[y+k] :-1;
return rx < ry;
};
sort(sa.begin(),sa.end(),cmp);
tmp[sa[0]] = 0;
for(int i = 1; i < n; i++){
tmp[sa[i]] = tmp[sa[i-1]]+(cmp(sa[i-1],sa[i])? 1 : 0);
}
swap(tmp,rnk);
}
return sa;
}
template <int THRESHOLD_NAIVE = 10,int THRESHOLD_DOUBLING = 40>
V<int> sa_is(const V<int>& s,int upper){
int n = int(s.size());
if(n == 0)return{};
if(n == 1)return{0};
if(n == 2){
if(s[0] < s[1]){
return{0,1};
}else{
return{1,0};
}
}
if(n < THRESHOLD_NAIVE){
return sa_naive(s);
}
if(n < THRESHOLD_DOUBLING){
return sa_doubling(s);
}
V<int> sa(n);
V<bool> ls(n);
for(int i = n-2; i >= 0; i--){
ls[i] =(s[i] == s[i+1])? ls[i+1] :(s[i] < s[i+1]);
}
V<int> sum_l(upper+1),sum_s(upper+1);
for(int i = 0; i < n; i++){
if(!ls[i]){
sum_s[s[i]]++;
}else{
sum_l[s[i]+1]++;
}
}
for(int i = 0; i <= upper; i++){
sum_s[i]+= sum_l[i];
if(i < upper)sum_l[i+1]+= sum_s[i];
}
auto induce = [&](const V<int>& lms){
fill(sa.begin(),sa.end(),-1);
V<int> buf(upper+1);
copy(sum_s.begin(),sum_s.end(),buf.begin());
for(auto d : lms){
if(d == n)continue;
sa[buf[s[d]]++] = d;
}
copy(sum_l.begin(),sum_l.end(),buf.begin());
sa[buf[s[n-1]]++] = n-1;
for(int i = 0; i < n; i++){
int v = sa[i];
if(v >= 1 && !ls[v-1]){
sa[buf[s[v-1]]++] = v-1;
}
}
copy(sum_l.begin(),sum_l.end(),buf.begin());
for(int i = n-1; i >= 0; i--){
int v = sa[i];
if(v >= 1 && ls[v-1]){
sa[--buf[s[v-1]+1]] = v-1;
}
}
};
V<int> lms_map(n+1,-1);
int m = 0;
for(int i = 1; i < n; i++){
if(!ls[i-1] && ls[i]){
lms_map[i] = m++;
}
}
V<int> lms;
lms.reserve(m);
for(int i = 1; i < n; i++){
if(!ls[i-1] && ls[i]){
lms.push_back(i);
}
}
induce(lms);
if(m){
V<int> sorted_lms;
sorted_lms.reserve(m);
for(int v : sa){
if(lms_map[v] !=-1)sorted_lms.push_back(v);
}
V<int> rec_s(m);
int rec_upper = 0;
rec_s[lms_map[sorted_lms[0]]] = 0;
for(int i = 1; i < m; i++){
int l = sorted_lms[i-1],r = sorted_lms[i];
int end_l =(lms_map[l]+1 < m)? lms[lms_map[l]+1] : n;
int end_r =(lms_map[r]+1 < m)? lms[lms_map[r]+1] : n;
bool same = true;
if(end_l-l != end_r-r){
same = false;
}else{
while(l < end_l){
if(s[l] != s[r]){
break;
}
l++;
r++;
}
if(l == n || s[l] != s[r])same = false;
}
if(!same)rec_upper++;
rec_s[lms_map[sorted_lms[i]]] = rec_upper;
}
auto rec_sa =
sa_is<THRESHOLD_NAIVE,THRESHOLD_DOUBLING>(rec_s,rec_upper);
for(int i = 0; i < m; i++){
sorted_lms[i] = lms[rec_sa[i]];
}
induce(sorted_lms);
}
return sa;
}
}
V<int> suffix_array(const V<int>& s,int upper){
assert(0 <= upper);
for(int d : s){
assert(0 <= d && d <= upper);
}
auto sa = internal::sa_is(s,upper);
return sa;
}
template <class T> V<int> suffix_array(const V<T>& s){
int n = int(s.size());
V<int> idx(n);
iota(idx.begin(),idx.end(),0);
sort(idx.begin(),idx.end(),[&](int l,int r){return s[l] < s[r];});
V<int> s2(n);
int now = 0;
for(int i = 0; i < n; i++){
if(i && s[idx[i-1]] != s[idx[i]])now++;
s2[idx[i]] = now;
}
return internal::sa_is(s2,now);
}
V<int> suffix_array(const string& s){
int n = int(s.size());
V<int> s2(n);
for(int i = 0; i < n; i++){
s2[i] = s[i];
}
return internal::sa_is(s2,255);
}
template <class T>
V<int> lcp_array(const V<T>& s,
const V<int>& sa){
int n = int(s.size());
assert(n >= 1);
V<int> rnk(n);
for(int i = 0; i < n; i++){
rnk[sa[i]] = i;
}
V<int> lcp(n-1);
int h = 0;
for(int i = 0; i < n; i++){
if(h > 0)h--;
if(rnk[i] == 0)continue;
int j = sa[rnk[i]-1];
for(; j+h < n && i+h < n; h++){
if(s[j+h] != s[i+h])break;
}
lcp[rnk[i]-1] = h;
}
return lcp;
}
V<int> lcp_array(const string& s,const V<int>& sa){
int n = int(s.size());
V<int> s2(n);
for(int i = 0; i < n; i++){
s2[i] = s[i];
}
return lcp_array(s2,sa);
}
template <class T> V<int> z_algorithm(const V<T>& s){
int n = int(s.size());
if(n == 0)return{};
V<int> z(n);
z[0] = 0;
for(int i = 1,j = 0; i < n; i++){
int& k = z[i];
k =(j+z[j] <= i)? 0 : min(j+z[j]-i,z[i-j]);
while(i+k < n && s[k] == s[i+k])k++;
if(j+z[j] < i+z[i])j = i;
}
z[0] = n;
return z;
}
V<int> z_algorithm(const string& s){
int n = int(s.size());
V<int> s2(n);
for(int i = 0; i < n; i++){
s2[i] = s[i];
}
return z_algorithm(s2);
}
struct two_sat{
public:
two_sat(): _n(0),scc(0){}
two_sat(int n): _n(n),_answer(n),scc(2 * n){}
void add_clause(int i,bool f,int j,bool g){
assert(0 <= i && i < _n);
assert(0 <= j && j < _n);
scc.add_edge(2 * i+(f ? 0 : 1),2 * j+(g ? 1 : 0));
scc.add_edge(2 * j+(g ? 0 : 1),2 * i+(f ? 1 : 0));
}
bool satisfiable(){
auto id = scc.scc_ids().second;
for(int i = 0; i < _n; i++){
if(id[2 * i] == id[2 * i+1])return false;
_answer[i] = id[2 * i] < id[2 * i+1];
}
return true;
}
V<bool> answer(){return _answer;}
private:
int _n;
V<bool> _answer;
internal::scc_graph scc;
};
}
#endif
