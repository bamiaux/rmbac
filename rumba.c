#define _POSIX_C_SOURCE 200809L
#include <assert.h>
#include <ctype.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#if !defined(__SIZEOF_INT128__)
#error "rumba-c currently requires a compiler with 128-bit integer support (GCC/Clang)"
#endif
__extension__ typedef __int128 i128;

typedef struct ArenaBlock { struct ArenaBlock *next; size_t used, cap; max_align_t _a; unsigned char data[]; } ArenaBlock;
typedef struct { ArenaBlock *head; } Arena;
static void arena_init(Arena *a){ a->head=NULL; }
static void arena_reset(Arena *a){ ArenaBlock *b=a->head; while(b){ArenaBlock*n=b->next; free(b); b=n;} a->head=NULL; }
static void *arena_alloc(Arena *a,size_t n){
    const size_t al=_Alignof(max_align_t); n=(n+al-1)&~(al-1);
    ArenaBlock*b=a->head;
    if(!b || b->used+n>b->cap){ size_t cap=n>65536?n:65536; b=malloc(sizeof(*b)+cap); if(!b){perror("malloc"); exit(2);} b->next=a->head;b->used=0;b->cap=cap;a->head=b; }
    void*p=b->data+b->used;b->used+=n;memset(p,0,n);return p;
}

typedef enum { E_VAR, E_CONST, E_NOT, E_SCALE, E_AND, E_OR, E_XOR, E_ADD, E_MUL } Kind;
typedef struct Expr Expr;
struct Expr { Kind k; union { size_t var; uint64_t c; Expr *unary; struct {uint64_t c; Expr*e;} scale; struct {size_t n; Expr **v;} list; } u; };

typedef struct { Arena arena; } Rumba;
static Expr* ex_new(Rumba*r,Kind k){Expr*e=arena_alloc(&r->arena,sizeof(*e));e->k=k;return e;}
static Expr* ex_var(Rumba*r,size_t v){Expr*e=ex_new(r,E_VAR);e->u.var=v;return e;}
static Expr* ex_const(Rumba*r,uint64_t c){Expr*e=ex_new(r,E_CONST);e->u.c=c;return e;}
static Expr* ex_unary(Rumba*r,Kind k,Expr*x){Expr*e=ex_new(r,k);e->u.unary=x;return e;}
static Expr* ex_scale_raw(Rumba*r,uint64_t c,Expr*x){Expr*e=ex_new(r,E_SCALE);e->u.scale.c=c;e->u.scale.e=x;return e;}
static Expr* ex_scale(Rumba*r,uint64_t c,Expr*x){if(c==0)return ex_const(r,0);if(c==1)return x;return ex_scale_raw(r,c,x);}
static Expr* ex_list(Rumba*r,Kind k,size_t n,Expr**v){Expr*e=ex_new(r,k);e->u.list.n=n;if(n){e->u.list.v=arena_alloc(&r->arena,n*sizeof(Expr*));memcpy(e->u.list.v,v,n*sizeof(Expr*));}return e;}
static Expr* ex2(Rumba*r,Kind k,Expr*a,Expr*b){Expr*v[2]={a,b};return ex_list(r,k,2,v);} 
static Expr* ex_neg(Rumba*r,Expr*x){return ex_scale(r,UINT64_MAX,x);} 
static uint64_t mask_n(unsigned n){return n>=64?UINT64_MAX:((UINT64_C(1)<<n)-1);}
static int64_t i64_from_bits(uint64_t x){int64_t v;memcpy(&v,&x,sizeof v);return v;}
static int64_t i64_wrap_sub(int64_t a,int64_t b){return i64_from_bits((uint64_t)a-(uint64_t)b);}
static int64_t i64_wrap_mul(int64_t a,int64_t b){return i64_from_bits((uint64_t)a*(uint64_t)b);}

static int ex_cmp(const Expr*a,const Expr*b);
static bool ex_eq(const Expr*a,const Expr*b){return ex_cmp(a,b)==0;}
static int cmp_u64(uint64_t a,uint64_t b){return a<b?-1:a>b?1:0;}
static int cmp_sz(size_t a,size_t b){return a<b?-1:a>b?1:0;}
static int ex_cmp(const Expr*a,const Expr*b){
    if(a->k!=b->k)return a->k<b->k?-1:1;
    switch(a->k){
      case E_VAR:return cmp_sz(a->u.var,b->u.var); case E_CONST:return cmp_u64(a->u.c,b->u.c);
      case E_NOT:return ex_cmp(a->u.unary,b->u.unary);
      case E_SCALE:{int c=cmp_u64(a->u.scale.c,b->u.scale.c);return c?c:ex_cmp(a->u.scale.e,b->u.scale.e);} 
      default:{size_t na=a->u.list.n,nb=b->u.list.n,n=na<nb?na:nb;for(size_t i=0;i<n;i++){int c=ex_cmp(a->u.list.v[i],b->u.list.v[i]);if(c)return c;}return cmp_sz(na,nb);} }
}
static int qcmp_exprptr(const void*pa,const void*pb){Expr*a=*(Expr*const*)pa,*b=*(Expr*const*)pb;return ex_cmp(a,b);} 
static size_t ex_size(const Expr*e){size_t s=1;switch(e->k){case E_NOT:s+=ex_size(e->u.unary);break;case E_SCALE:s+=ex_size(e->u.scale.e);break;case E_AND:case E_OR:case E_XOR:case E_ADD:case E_MUL:for(size_t i=0;i<e->u.list.n;i++)s+=ex_size(e->u.list.v[i]);break;default:break;}return s;}
static size_t ex_maxvar(const Expr*e,bool*any){switch(e->k){case E_VAR:*any=true;return e->u.var;case E_NOT:return ex_maxvar(e->u.unary,any);case E_SCALE:return ex_maxvar(e->u.scale.e,any);case E_AND:case E_OR:case E_XOR:case E_ADD:case E_MUL:{size_t m=0;for(size_t i=0;i<e->u.list.n;i++){bool a=false;size_t q=ex_maxvar(e->u.list.v[i],&a);if(a){*any=true;if(q>m)m=q;}}return m;}default:return 0;}}
static uint64_t ex_eval(const Expr*e,const uint64_t*vars,size_t nvars){switch(e->k){case E_VAR:return e->u.var<nvars?vars[e->u.var]:0;case E_CONST:return e->u.c;case E_NOT:return ~ex_eval(e->u.unary,vars,nvars);case E_SCALE:return e->u.scale.c*ex_eval(e->u.scale.e,vars,nvars);case E_AND:{uint64_t x=UINT64_MAX;for(size_t i=0;i<e->u.list.n;i++)x&=ex_eval(e->u.list.v[i],vars,nvars);return x;}case E_OR:{uint64_t x=0;for(size_t i=0;i<e->u.list.n;i++)x|=ex_eval(e->u.list.v[i],vars,nvars);return x;}case E_XOR:{uint64_t x=0;for(size_t i=0;i<e->u.list.n;i++)x^=ex_eval(e->u.list.v[i],vars,nvars);return x;}case E_ADD:{uint64_t x=0;for(size_t i=0;i<e->u.list.n;i++)x+=ex_eval(e->u.list.v[i],vars,nvars);return x;}case E_MUL:{uint64_t x=1;for(size_t i=0;i<e->u.list.n;i++)x*=ex_eval(e->u.list.v[i],vars,nvars);return x;}}return 0;}

typedef struct { Expr **v; size_t n,cap; } EV;
static void ev_push(EV*x,Expr*e){if(x->n==x->cap){x->cap=x->cap?x->cap*2:8;x->v=realloc(x->v,x->cap*sizeof(*x->v));if(!x->v){perror("realloc");exit(2);}}x->v[x->n++]=e;}
static void ev_free(EV*x){free(x->v);x->v=NULL;x->n=x->cap=0;}

typedef struct { char *s; size_t n,cap; } SB;
static void sb_init(SB*b){b->s=NULL;b->n=b->cap=0;}
static void sb_need(SB*b,size_t add){size_t need=b->n+add+1;if(need>b->cap){size_t c=b->cap?b->cap:128;while(c<need)c*=2;b->s=realloc(b->s,c);if(!b->s){perror("realloc");exit(2);}b->cap=c;}}
static void sb_puts(SB*b,const char*s){size_t n=strlen(s);sb_need(b,n);memcpy(b->s+b->n,s,n);b->n+=n;b->s[b->n]=0;}
static void sb_printf(SB*b,const char*fmt,...){va_list ap;va_start(ap,fmt);va_list aq;va_copy(aq,ap);int n=vsnprintf(NULL,0,fmt,aq);va_end(aq);if(n>0){sb_need(b,(size_t)n);vsnprintf(b->s+b->n,b->cap-b->n,fmt,ap);b->n+=(size_t)n;}va_end(ap);} 
static int precedence(const Expr*e){if((e->k>=E_AND&&e->k<=E_MUL)&&e->u.list.n==1)return precedence(e->u.list.v[0]);switch(e->k){case E_VAR:case E_CONST:return 0;case E_NOT:return 2;case E_MUL:case E_SCALE:return 3;case E_ADD:return 4;case E_AND:return 8;case E_XOR:return 9;case E_OR:return 10;}return 99;}
static void repr_rec(SB*b,const Expr*e,unsigned n,uint64_t mask,bool hex,const Expr*parent);
static void repr_const(SB*b,uint64_t c,unsigned n,uint64_t mask,bool hex){uint64_t v=c&mask;uint64_t sign=UINT64_C(1)<<(n-1);if(v&sign){uint64_t mag=(~v+1)&mask;if(hex)sb_printf(b,"(-0x%" PRIx64 ")",mag);else sb_printf(b,"(-%" PRIu64 ")",mag);}else{if(hex)sb_printf(b,"0x%" PRIx64,v);else sb_printf(b,"%" PRIu64,v);}}
static void repr_child(SB*b,const Expr*c,unsigned n,uint64_t mask,bool hex,const Expr*p){bool par=precedence(p)<precedence(c);if(par)sb_puts(b,"(");repr_rec(b,c,n,mask,hex,NULL);if(par)sb_puts(b,")");}
static void repr_rec(SB*b,const Expr*e,unsigned n,uint64_t mask,bool hex,const Expr*parent){(void)parent;if((e->k>=E_AND&&e->k<=E_MUL)&&e->u.list.n==1){repr_rec(b,e->u.list.v[0],n,mask,hex,NULL);return;}switch(e->k){case E_VAR:sb_printf(b,"v%zu",e->u.var);return;case E_CONST:repr_const(b,e->u.c,n,mask,hex);return;case E_NOT:sb_puts(b,"~ ");repr_child(b,e->u.unary,n,mask,hex,e);return;case E_SCALE:repr_const(b,e->u.scale.c,n,mask,hex);sb_puts(b," * ");repr_child(b,e->u.scale.e,n,mask,hex,e);return;case E_ADD:{uint64_t sign=UINT64_C(1)<<(n-1);for(size_t i=0;i<e->u.list.n;i++){Expr*t=e->u.list.v[i];bool neg=false;uint64_t mag=0;Expr*inner=NULL;if(t->k==E_CONST && (t->u.c&mask&sign)){neg=true;mag=(~t->u.c+1)&mask;}else if(t->k==E_SCALE&&(t->u.scale.c&mask&sign)){neg=true;mag=(~t->u.scale.c+1)&mask;inner=t->u.scale.e;}if(i==0){if(neg)sb_puts(b,"-");}else sb_puts(b,neg?" - ":" + ");if(neg){if(inner){if(mag!=1){repr_const(b,mag,n,mask,hex);sb_puts(b," * ");}Expr fake={.k=E_MUL};repr_child(b,inner,n,mask,hex,&fake);}else repr_const(b,mag,n,mask,hex);}else repr_child(b,t,n,mask,hex,e);}return;}default:{const char*op=e->k==E_AND?" & ":e->k==E_OR?" | ":e->k==E_XOR?" ^ ":" * ";for(size_t i=0;i<e->u.list.n;i++){if(i)sb_puts(b,op);repr_child(b,e->u.list.v[i],n,mask,hex,e);}return;}}}
static char *ex_repr(const Expr*e,unsigned n,bool hex){SB b;sb_init(&b);repr_rec(&b,e,n,mask_n(n),hex,NULL);if(!b.s){b.s=strdup("");}return b.s;}

/* parser: same precedence/grammar as expr.pest */
typedef struct { Rumba*r; const char*s; size_t p,n; char err[256]; } Parser;
static void ps_ws(Parser*p){while(p->p<p->n&&(p->s[p->p]==' '||p->s[p->p]=='\t'||p->s[p->p]=='\n'||p->s[p->p]=='\r'))p->p++;}
static bool ps_take(Parser*p,char c){ps_ws(p);if(p->p<p->n&&p->s[p->p]==c){p->p++;return true;}return false;}
static Expr* parse_or(Parser*p);
static Expr* parse_atom(Parser*p){ps_ws(p);if(p->p>=p->n){snprintf(p->err,sizeof p->err,"unexpected end");return NULL;}if(ps_take(p,'(')){Expr*e=parse_or(p);if(!e||!ps_take(p,')')){if(!p->err[0])snprintf(p->err,sizeof p->err,"expected ')' at %zu",p->p);return NULL;}return e;}size_t st=p->p;if(p->s[p->p]=='v'){p->p++;size_t d=p->p;while(p->p<p->n&&isdigit((unsigned char)p->s[p->p]))p->p++;if(p->p==d){snprintf(p->err,sizeof p->err,"bad variable at %zu",st);return NULL;}char buf[64];size_t z=p->p-d;if(z>=sizeof buf){snprintf(p->err,sizeof p->err,"variable index too long");return NULL;}memcpy(buf,p->s+d,z);buf[z]=0;char*end;unsigned long long v=strtoull(buf,&end,10);if(*end){return NULL;}return ex_var(p->r,(size_t)v);}if(isdigit((unsigned char)p->s[p->p])){int base=10;if(p->p+2<=p->n&&p->s[p->p]=='0'&&p->s[p->p+1]=='x'){base=16;p->p+=2;st=p->p;while(p->p<p->n&&isxdigit((unsigned char)p->s[p->p]))p->p++;}else{while(p->p<p->n&&isdigit((unsigned char)p->s[p->p]))p->p++;}size_t z=p->p-st;char*tmp=malloc(z+1);memcpy(tmp,p->s+st,z);tmp[z]=0;char*end;unsigned long long v=strtoull(tmp,&end,base);bool ok=*end==0;free(tmp);if(!ok){snprintf(p->err,sizeof p->err,"bad integer");return NULL;}return ex_const(p->r,(uint64_t)v);}snprintf(p->err,sizeof p->err,"unexpected character '%c' at %zu",p->s[p->p],p->p);return NULL;}
static Expr* parse_unary(Parser*p){ps_ws(p);if(ps_take(p,'~')||ps_take(p,'!')){Expr*x=parse_unary(p);return x?ex_unary(p->r,E_NOT,x):NULL;}if(ps_take(p,'-')){Expr*x=parse_unary(p);return x?ex_neg(p->r,x):NULL;}return parse_atom(p);}
static Expr* parse_mul(Parser*p){Expr*a=parse_unary(p);if(!a)return NULL;EV v={0};ev_push(&v,a);while(ps_take(p,'*')){Expr*b=parse_unary(p);if(!b){ev_free(&v);return NULL;}ev_push(&v,b);}if(v.n==1){a=v.v[0];ev_free(&v);return a;}Expr*e=ex_list(p->r,E_MUL,v.n,v.v);ev_free(&v);return e;}
static Expr* parse_add(Parser*p){Expr*a=parse_mul(p);if(!a)return NULL;EV v={0};ev_push(&v,a);for(;;){ps_ws(p);char op=p->p<p->n?p->s[p->p]:0;if(op!='+'&&op!='-')break;p->p++;Expr*b=parse_mul(p);if(!b){ev_free(&v);return NULL;}ev_push(&v,op=='-'?ex_neg(p->r,b):b);}if(v.n==1){a=v.v[0];ev_free(&v);return a;}Expr*e=ex_list(p->r,E_ADD,v.n,v.v);ev_free(&v);return e;}
static Expr* parse_nary(Parser*p,Expr*(*sub)(Parser*),char op,Kind k){Expr*a=sub(p);if(!a)return NULL;EV v={0};ev_push(&v,a);while(ps_take(p,op)){Expr*b=sub(p);if(!b){ev_free(&v);return NULL;}ev_push(&v,b);}if(v.n==1){a=v.v[0];ev_free(&v);return a;}Expr*e=ex_list(p->r,k,v.n,v.v);ev_free(&v);return e;}
static Expr* parse_and(Parser*p){return parse_nary(p,parse_add,'&',E_AND);}static Expr*parse_xor(Parser*p){return parse_nary(p,parse_and,'^',E_XOR);}static Expr*parse_or(Parser*p){return parse_nary(p,parse_xor,'|',E_OR);}
static Expr *parse_expr(Rumba*r,const char*s,char*err,size_t errcap){Parser p={.r=r,.s=s,.n=strlen(s)};Expr*e=parse_or(&p);ps_ws(&p);if(e&&p.p!=p.n){snprintf(p.err,sizeof p.err,"trailing input at %zu",p.p);e=NULL;}if(!e&&err&&errcap)snprintf(err,errcap,"%s",p.err[0]?p.err:"parse error");return e;}

/* reduction */
static Expr* reduce_m(Rumba*r,Expr*e,uint64_t mask);
static void flatten_reduced(EV*out,Expr*q,Kind k){if(q->k==k){for(size_t i=0;i<q->u.list.n;i++)flatten_reduced(out,q->u.list.v[i],k);}else ev_push(out,q);}
static void flatten_kind(Rumba*r,EV*out,Expr*e,Kind k,uint64_t mask){flatten_reduced(out,reduce_m(r,e,mask),k);}
static Expr* reduce_not(Rumba*r,Expr*x,uint64_t mask){if(x->k==E_NOT)return reduce_m(r,x->u.unary,mask);if(x->k==E_CONST)return ex_const(r,~x->u.c);if(x->k==E_AND||x->k==E_OR){Kind k=x->k==E_AND?E_OR:E_AND;EV v={0};for(size_t i=0;i<x->u.list.n;i++)ev_push(&v,reduce_m(r,ex_unary(r,E_NOT,x->u.list.v[i]),mask));Expr*q=ex_list(r,k,v.n,v.v);ev_free(&v);return q;}return ex_unary(r,E_NOT,reduce_m(r,x,mask));}
static Expr* reduce_scale(Rumba*r,uint64_t c,Expr*x,uint64_t mask){c&=mask;if(c==0)return ex_const(r,0);if(c==1)return reduce_m(r,x,mask);x=reduce_m(r,x,mask);if(x->k==E_CONST)return ex_const(r,c*x->u.c&mask);if(x->k==E_SCALE){uint64_t q=c*x->u.scale.c&mask;return q==0?ex_const(r,0):q==1?x->u.scale.e:ex_scale(r,q,x->u.scale.e);}if(x->k==E_ADD){EV v={0};for(size_t i=0;i<x->u.list.n;i++)ev_push(&v,ex_scale(r,c,x->u.list.v[i]));Expr*q=reduce_m(r,ex_list(r,E_ADD,v.n,v.v),mask);ev_free(&v);return q;}return ex_scale(r,c,x);}
static Expr* reduce_andor(Rumba*r,Expr*e,uint64_t mask,bool is_and){EV v={0};uint64_t c=is_and?mask:0;for(size_t i=0;i<e->u.list.n;i++){EV t={0};flatten_kind(r,&t,e->u.list.v[i],e->k,mask);for(size_t j=0;j<t.n;j++){Expr*q=t.v[j];if(q->k==E_CONST){if(is_and)c&=q->u.c;else c|=q->u.c;}else ev_push(&v,q);}ev_free(&t);}c&=mask;if(is_and&&c==0){ev_free(&v);return ex_const(r,0);}if((is_and&&c!=mask)||(!is_and&&c!=0))ev_push(&v,ex_const(r,c));/* Rust reduce.rs distributes And over Xor and Or over And before deduplication. */Kind child=is_and?E_XOR:E_AND;for(size_t i=0;i<v.n;i++)if(v.v[i]->k==child){Expr*ch=v.v[i];EV out={0};for(size_t j=0;j<ch->u.list.n;j++){EV copy={0};for(size_t k=0;k<v.n;k++)ev_push(&copy,k==i?ch->u.list.v[j]:v.v[k]);ev_push(&out,ex_list(r,e->k,copy.n,copy.v));ev_free(&copy);}Expr*q=reduce_m(r,ex_list(r,child,out.n,out.v),mask);ev_free(&out);ev_free(&v);return q;}if(v.n>1)qsort(v.v,v.n,sizeof(Expr*),qcmp_exprptr);size_t w=0;for(size_t i=0;i<v.n;i++)if(i==0||!ex_eq(v.v[i],v.v[i-1]))v.v[w++]=v.v[i];v.n=w;if(v.n==0){ev_free(&v);return ex_const(r,is_and?UINT64_MAX:0);}if(v.n==1){Expr*q=v.v[0];ev_free(&v);return q;}Expr*q=ex_list(r,e->k,v.n,v.v);ev_free(&v);return q;}
static Expr* reduce_xor(Rumba*r,Expr*e,uint64_t mask){EV v={0};uint64_t c=0;for(size_t i=0;i<e->u.list.n;i++){EV t={0};flatten_kind(r,&t,e->u.list.v[i],E_XOR,mask);for(size_t j=0;j<t.n;j++){Expr*q=t.v[j];if(q->k==E_CONST)c^=q->u.c;else ev_push(&v,q);}ev_free(&t);}c&=mask;if(c)ev_push(&v,ex_const(r,c));if(v.n>1)qsort(v.v,v.n,sizeof(Expr*),qcmp_exprptr);EV o={0};for(size_t i=0;i<v.n;){size_t j=i+1;while(j<v.n&&ex_eq(v.v[i],v.v[j]))j++;if((j-i)&1)ev_push(&o,v.v[i]);i=j;}ev_free(&v);if(o.n==0){ev_free(&o);return ex_const(r,0);}if(o.n==1){Expr*q=o.v[0];ev_free(&o);return q;}Expr*q=ex_list(r,E_XOR,o.n,o.v);ev_free(&o);return q;}
static Expr* group_terms(Rumba*r,EV*v,uint64_t mask){typedef struct{Expr*core;uint64_t c;}T;size_t initial=v->n;T*t=NULL;size_t n=0,cap=0;for(size_t i=0;i<v->n;i++){Expr*e=v->v[i];uint64_t c=1;Expr*core=e;if(e->k==E_SCALE){c=e->u.scale.c;core=e->u.scale.e;}size_t j;for(j=0;j<n;j++)if(ex_eq(t[j].core,core))break;if(j==n){if(n==cap){cap=cap?cap*2:8;t=realloc(t,cap*sizeof(*t));}t[n++]=(T){core,0};}t[j].c+=c;}EV o={0};for(size_t i=0;i<n;i++){uint64_t c=t[i].c&mask;if(c)ev_push(&o,ex_scale(r,c,t[i].core));}free(t);if(o.n>1)qsort(o.v,o.n,sizeof(Expr*),qcmp_exprptr);Expr*q;if(initial>o.n){q=reduce_m(r,ex_list(r,E_ADD,o.n,o.v),mask);}else if(o.n==0)q=ex_const(r,0);else if(o.n==1)q=o.v[0];else q=ex_list(r,E_ADD,o.n,o.v);ev_free(&o);return q;}
static Expr* reduce_add(Rumba*r,Expr*e,uint64_t mask){if(mask==1){Expr*q=ex_list(r,E_XOR,e->u.list.n,e->u.list.v);return reduce_xor(r,q,mask);}EV v={0};uint64_t c=0;for(size_t i=0;i<e->u.list.n;i++){EV t={0};flatten_kind(r,&t,e->u.list.v[i],E_ADD,mask);for(size_t j=0;j<t.n;j++){Expr*q=t.v[j];if(q->k==E_CONST)c+=q->u.c;else ev_push(&v,q);}ev_free(&t);}c&=mask;if(c)ev_push(&v,ex_const(r,c));Expr*q=group_terms(r,&v,mask);ev_free(&v);return q;}
static Expr* reduce_mul(Rumba*r,Expr*e,uint64_t mask){if(mask==1){Expr*q=ex_list(r,E_AND,e->u.list.n,e->u.list.v);return reduce_andor(r,q,mask,true);}EV v={0};uint64_t c=1;for(size_t i=0;i<e->u.list.n;i++){EV t={0};flatten_kind(r,&t,e->u.list.v[i],E_MUL,mask);for(size_t j=0;j<t.n;j++){Expr*q=t.v[j];if(q->k==E_CONST)c*=q->u.c;else if(q->k==E_SCALE){c*=q->u.scale.c;ev_push(&v,q->u.scale.e);}else ev_push(&v,q);}ev_free(&t);}c&=mask;if(c==0){ev_free(&v);return ex_const(r,0);}/* distribute over first Add */for(size_t i=0;i<v.n;i++)if(v.v[i]->k==E_ADD){EV sum={0};Expr*ad=v.v[i];for(size_t j=0;j<ad->u.list.n;j++){EV p={0};for(size_t k=0;k<v.n;k++)ev_push(&p,k==i?ad->u.list.v[j]:v.v[k]);ev_push(&sum,ex_list(r,E_MUL,p.n,p.v));ev_free(&p);}Expr*q=reduce_m(r,ex_scale(r,c,ex_list(r,E_ADD,sum.n,sum.v)),mask);ev_free(&sum);ev_free(&v);return q;}if(v.n>1)qsort(v.v,v.n,sizeof(Expr*),qcmp_exprptr);Expr*q;if(v.n==0)q=ex_const(r,c);else if(v.n==1)q=ex_scale(r,c,v.v[0]);else q=ex_scale(r,c,ex_list(r,E_MUL,v.n,v.v));ev_free(&v);return q;}
static Expr* reduce_m(Rumba*r,Expr*e,uint64_t mask){switch(e->k){case E_VAR:return e;case E_CONST:return ex_const(r,e->u.c&mask);case E_NOT:return reduce_not(r,e->u.unary,mask);case E_SCALE:return reduce_scale(r,e->u.scale.c,e->u.scale.e,mask);case E_AND:return reduce_andor(r,e,mask,true);case E_OR:return reduce_andor(r,e,mask,false);case E_XOR:return reduce_xor(r,e,mask);case E_ADD:return reduce_add(r,e,mask);case E_MUL:return reduce_mul(r,e,mask);}return e;}

/* basic solver */
typedef struct HGKey HGKey;
struct HGKey { size_t height; Kind k; size_t var; uint64_t c; HGKey *child; size_t n; HGKey **children; };
typedef struct { size_t var; Expr *def; HGKey *gauge_key; } Hidden;
typedef struct Solver { Rumba*r; unsigned n; uint64_t mask; size_t t,degree; Hidden*h;size_t hn,hcap; unsigned depth; } Solver;
static Expr* solver_solve(Solver*s,Expr*e,bool*ok);
static Expr *simplify_inner(Rumba*r,Expr*e,unsigned n,unsigned depth,bool*ok);
static void hidden_push(Solver*s,size_t v,Expr*d,HGKey*k){if(s->hn==s->hcap){s->hcap=s->hcap?s->hcap*2:8;s->h=realloc(s->h,s->hcap*sizeof(*s->h));if(!s->h){perror("realloc");exit(2);}}s->h[s->hn++]=(Hidden){v,d,k};}
static Hidden* hidden_entry_by_var(Solver*s,size_t v){for(size_t i=0;i<s->hn;i++)if(s->h[i].var==v)return &s->h[i];return NULL;}
static Expr* hidden_by_var(Solver*s,size_t v){Hidden*h=hidden_entry_by_var(s,v);return h?h->def:NULL;}
static bool hidden_find_expr(Solver*s,Expr*e,size_t*out){for(size_t i=0;i<s->hn;i++)if(ex_eq(s->h[i].def,e)){*out=s->h[i].var;return true;}return false;}
static Expr* complement_expr(Rumba*r,Expr*e,uint64_t mask){return reduce_m(r,ex2(r,E_ADD,ex_neg(r,e),ex_const(r,UINT64_MAX)),mask);}

/* Hidden Gauge: exact structural complement-orbit interning. */
static int hg_cmp(const HGKey*a,const HGKey*b);
static int hg_ptr_cmp_q(const void*aa,const void*bb){HGKey*a=*(HGKey*const*)aa,*b=*(HGKey*const*)bb;return hg_cmp(a,b);}
static int hg_cmp(const HGKey*a,const HGKey*b){if(a==b)return 0;if(a->height!=b->height)return a->height<b->height?-1:1;if(a->k!=b->k)return a->k<b->k?-1:1;switch(a->k){case E_VAR:return cmp_sz(a->var,b->var);case E_CONST:return cmp_u64(a->c,b->c);case E_NOT:return hg_cmp(a->child,b->child);case E_SCALE:{int c=cmp_u64(a->c,b->c);return c?c:hg_cmp(a->child,b->child);}default:{size_t n=a->n<b->n?a->n:b->n;for(size_t i=0;i<n;i++){int c=hg_cmp(a->children[i],b->children[i]);if(c)return c;}return cmp_sz(a->n,b->n);}}}
static HGKey* hg_new(Solver*s,Kind k){HGKey*q=arena_alloc(&s->r->arena,sizeof(*q));q->k=k;return q;}
static HGKey* hg_key_of(Solver*s,Expr*e){if(e->k==E_VAR){Hidden*h=hidden_entry_by_var(s,e->u.var);if(h&&h->gauge_key)return h->gauge_key;HGKey*q=hg_new(s,E_VAR);q->var=e->u.var;return q;}if(e->k==E_CONST){HGKey*q=hg_new(s,E_CONST);q->c=e->u.c&s->mask;return q;}if(e->k==E_NOT){HGKey*q=hg_new(s,E_NOT);q->child=hg_key_of(s,e->u.unary);q->height=q->child->height+1;return q;}if(e->k==E_SCALE){HGKey*q=hg_new(s,E_SCALE);q->c=e->u.scale.c&s->mask;q->child=hg_key_of(s,e->u.scale.e);q->height=q->child->height+1;return q;}HGKey*q=hg_new(s,e->k);q->n=e->u.list.n;if(q->n){q->children=arena_alloc(&s->r->arena,q->n*sizeof(*q->children));size_t mh=0;for(size_t i=0;i<q->n;i++){q->children[i]=hg_key_of(s,e->u.list.v[i]);if(q->children[i]->height>mh)mh=q->children[i]->height;}if(q->n>1)qsort(q->children,q->n,sizeof(*q->children),hg_ptr_cmp_q);q->height=mh+1;}return q;}
static bool hg_find_orbit(Solver*s,HGKey*k,size_t*out){for(size_t i=0;i<s->hn;i++)if(s->h[i].gauge_key&&hg_cmp(s->h[i].gauge_key,k)==0){*out=s->h[i].var;return true;}return false;}
static Expr* hidden_intern(Solver*s,Expr*e){uint64_t mask=s->mask;size_t v;if(hidden_find_expr(s,e,&v))return ex_var(s->r,v);Expr*note=complement_expr(s->r,e,mask);if(hidden_find_expr(s,note,&v))return ex_unary(s->r,E_NOT,ex_var(s->r,v));HGKey*k=hg_key_of(s,e),*nk=hg_key_of(s,note);bool complemented=hg_cmp(nk,k)<0;HGKey*orbit=complemented?nk:k;if(hg_find_orbit(s,orbit,&v)){Expr*q=ex_var(s->r,v);return complemented?ex_unary(s->r,E_NOT,q):q;}v=s->t++;Expr*definition=complemented?note:e;hidden_push(s,v,definition,orbit);Expr*q=ex_var(s->r,v);return complemented?ex_unary(s->r,E_NOT,q):q;}

typedef struct { size_t *fwd,*rev,nf,nr; } VMap;
static Expr* reduce_vars_rec(Rumba*r,Expr*e,VMap*m){if(e->k==E_VAR){size_t v=e->u.var;if(v>=m->nf){size_t old=m->nf,newn=v+1;m->fwd=realloc(m->fwd,newn*sizeof(size_t));for(size_t i=old;i<newn;i++)m->fwd[i]=SIZE_MAX;m->nf=newn;}if(m->fwd[v]==SIZE_MAX){m->fwd[v]=m->nr;m->rev=realloc(m->rev,(m->nr+1)*sizeof(size_t));m->rev[m->nr++]=v;}return ex_var(r,m->fwd[v]);}switch(e->k){case E_CONST:return e;case E_NOT:return ex_unary(r,E_NOT,reduce_vars_rec(r,e->u.unary,m));case E_SCALE:return ex_scale(r,e->u.scale.c,reduce_vars_rec(r,e->u.scale.e,m));default:{EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,reduce_vars_rec(r,e->u.list.v[i],m));Expr*q=ex_list(r,e->k,v.n,v.v);ev_free(&v);return q;}}}
static Expr* restore_vars_rec(Rumba*r,Expr*e,VMap*m,bool*ok){if(e->k==E_VAR){if(e->u.var>=m->nr){*ok=false;return e;}return ex_var(r,m->rev[e->u.var]);}switch(e->k){case E_CONST:return e;case E_NOT:return ex_unary(r,E_NOT,restore_vars_rec(r,e->u.unary,m,ok));case E_SCALE:return ex_scale(r,e->u.scale.c,restore_vars_rec(r,e->u.scale.e,m,ok));default:{EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,restore_vars_rec(r,e->u.list.v[i],m,ok));Expr*q=ex_list(r,e->k,v.n,v.v);ev_free(&v);return q;}}}
static uint64_t* truth_table(Expr*e,size_t t,uint64_t mask){if(t>20)return NULL;size_t sz=((size_t)1)<<t;uint64_t*tt=malloc(sz*sizeof(uint64_t));uint64_t*vars=calloc(t?t:1,sizeof(uint64_t));if(!tt||!vars){perror("malloc");exit(2);}for(size_t i=0;i<sz;i++){size_t q=i;for(size_t j=0;j<t;j++){vars[j]=q&1;q>>=1;}tt[i]=ex_eval(e,vars,t)&mask;}free(vars);return tt;}
static void sub_coeff(uint64_t*tt,size_t len,uint64_t coeff,size_t index,size_t*sub,size_t ns){size_t gp=((size_t)1)<<sub[0],period=gp*2;for(size_t st=index;st<len;st+=period){size_t end=st+gp;if(end>len)end=len;for(size_t i=st;i<end;i++){bool yes=true;for(size_t j=1;j<ns;j++)if(((i>>sub[j])&1)==0){yes=false;break;}if(ns==1||yes)tt[i]-=coeff;}}}
static Expr* make_conjunction_sum(Solver*s,uint64_t*sig,size_t t){Rumba*r=s->r;EV terms={0};size_t sz=((size_t)1)<<t;uint64_t c=sig[0];if(c){ev_push(&terms,ex_const(r,c));for(size_t i=0;i<sz;i++)sig[i]-=c;}size_t*sub=malloc((t?t:1)*sizeof(size_t));for(size_t idx=1;idx<sz;idx++){uint64_t coeff=sig[idx]&s->mask;if(!coeff)continue;size_t ns=0;for(size_t i=0;i<t;i++)if((idx>>i)&1)sub[ns++]=i;EV ands={0};for(size_t j=0;j<ns;j++)ev_push(&ands,ex_var(r,sub[j]));Expr*conj=ands.n==1?ands.v[0]:ex_list(r,E_AND,ands.n,ands.v);ev_free(&ands);ev_push(&terms,coeff==1?conj:ex_scale(r,coeff,conj));sub_coeff(sig,sz,coeff,idx,sub,ns);}free(sub);Expr*q;if(terms.n==0)q=ex_const(r,0);else if(terms.n==1)q=terms.v[0];else q=ex_list(r,E_ADD,terms.n,terms.v);ev_free(&terms);return q;}
static Expr* solve_linear(Solver*s,Expr*e,bool from_poly,bool*ok){(void)from_poly;VMap m={0};Expr*red=reduce_vars_rec(s->r,e,&m);size_t t=m.nr;if(t>20){*ok=false;free(m.fwd);free(m.rev);return e;}uint64_t*sig=truth_table(red,t,s->mask);Expr*q=make_conjunction_sum(s,sig,t);free(sig);q=restore_vars_rec(s->r,q,&m,ok);free(m.fwd);free(m.rev);return q;}
static bool is_bitwise_rec(Expr*e,uint64_t mask){switch(e->k){case E_CONST:return ((e->u.c&mask)==0)||((e->u.c&mask)==mask);case E_VAR:return true;case E_NOT:return is_bitwise_rec(e->u.unary,mask);case E_AND:case E_OR:case E_XOR:for(size_t i=0;i<e->u.list.n;i++)if(!is_bitwise_rec(e->u.list.v[i],mask))return false;return true;default:return false;}}
static bool is_scaled_bitwise(Expr*e,uint64_t mask){if(e->k==E_CONST)return true;if(e->k==E_SCALE)return is_bitwise_rec(e->u.scale.e,mask);return is_bitwise_rec(e,mask);}
static bool solver_is_linear(Solver*s,Expr*e){if(e->k==E_ADD){for(size_t i=0;i<e->u.list.n;i++)if(!is_scaled_bitwise(e->u.list.v[i],s->mask))return false;return true;}return is_scaled_bitwise(e,s->mask);}
static bool signature_bitwise(uint64_t*sig,size_t len,uint64_t mask){uint64_t m1=mask,m2=mask-1;if(sig[0]==0){for(size_t i=0;i<len;i++)if(sig[i]!=0&&sig[i]!=1)return false;return true;}if(sig[0]==m1){for(size_t i=0;i<len;i++)if(sig[i]!=m1&&sig[i]!=m2)return false;return true;}return false;}
static int64_t signed_n(uint64_t x,unsigned n){if(n==0)return 0;uint64_t m=mask_n(n),v=x&m;if(n<64&&(v&(UINT64_C(1)<<(n-1))))v|=~m;return i64_from_bits(v);}
static bool find_lambda(uint64_t*x,uint64_t*y,size_t len,int64_t a,int64_t b,unsigned n,uint64_t*out){bool have=false;int64_t cand[2]={0,0};bool cv[2]={false,false};for(size_t i=0;i<len;i++){int64_t xi=signed_n(x[i],n),yi=signed_n(y[i],n);if(yi==0){if(xi==a||xi==b)continue;return false;}int64_t vals[2]={0,0},d[2]={i64_wrap_sub(xi,a),i64_wrap_sub(xi,b)};bool vv[2]={false,false};for(int j=0;j<2;j++){if(yi==-1&&d[j]==INT64_MIN)continue;if(d[j]%yi==0){vv[j]=true;vals[j]=d[j]/yi;}}if(!have){for(int j=0;j<2;j++)if(vv[j]){cand[j]=vals[j];cv[j]=true;}have=true;}else{bool ncv[2]={false,false};int64_t nc[2]={0,0};int k=0;for(int j=0;j<2;j++)if(vv[j])for(int q=0;q<2;q++)if(cv[q]&&vals[j]==cand[q]&&k<2){ncv[k]=true;nc[k++]=vals[j];}memcpy(cv,ncv,sizeof cv);memcpy(cand,nc,sizeof cand);if(!cv[0]&&!cv[1])return false;}}if(!have){*out=0;return true;}for(int j=0;j<2;j++)if(cv[j]&&i64_wrap_sub(signed_n(x[0],n),i64_wrap_mul(cand[j],signed_n(y[0],n)))==a){*out=((uint64_t)cand[j])&mask_n(n);return true;}return false;}
static bool i128_mul_checked(i128 a,i128 b,i128*out){return !__builtin_mul_overflow(a,b,out);}static bool i128_sub_checked(i128 a,i128 b,i128*out){return !__builtin_sub_overflow(a,b,out);}
static bool find_two_lambdas(uint64_t*x,uint64_t*y,uint64_t*z,size_t len,int64_t a,int64_t b,unsigned n,uint64_t*oy,uint64_t*oz){size_t base=SIZE_MAX;for(size_t i=0;i<len;i++)if(signed_n(y[i],n)!=0||signed_n(z[i],n)!=0){base=i;break;}if(base==SIZE_MAX)return false;int64_t targets[2]={a,b};const i128 i128_min=-(((i128)1)<<126)-(((i128)1)<<126);for(size_t second=0;second<len;second++){int64_t y0=signed_n(y[base],n),z0=signed_n(z[base],n),y1=signed_n(y[second],n),z1=signed_n(z[second],n);i128 p0,p1,det;if(!i128_mul_checked((i128)y0,(i128)z1,&p0)||!i128_mul_checked((i128)y1,(i128)z0,&p1)||!i128_sub_checked(p0,p1,&det)||det==0)continue;for(int i=0;i<2;i++)for(int j=0;j<2;j++){i128 rhs0=(i128)signed_n(x[base],n)-targets[i],rhs1=(i128)signed_n(x[second],n)-targets[j],a0,a1,ny,nz;if(!i128_mul_checked(rhs0,(i128)z1,&a0)||!i128_mul_checked(rhs1,(i128)z0,&a1)||!i128_sub_checked(a0,a1,&ny))continue;if(!i128_mul_checked((i128)y0,rhs1,&a0)||!i128_mul_checked((i128)y1,rhs0,&a1)||!i128_sub_checked(a0,a1,&nz))continue;if(det==-1&&(ny==i128_min||nz==i128_min))continue;if(ny%det||nz%det)continue;i128 ly=ny/det,lz=nz/det;if(ly<INT64_MIN||ly>INT64_MAX||lz<INT64_MIN||lz>INT64_MAX)continue;int64_t yy=(int64_t)ly,zz=(int64_t)lz;bool good=true;for(size_t q=0;q<len;q++){int64_t val=i64_wrap_sub(i64_wrap_sub(signed_n(x[q],n),i64_wrap_mul(yy,signed_n(y[q],n))),i64_wrap_mul(zz,signed_n(z[q],n)));if(q==0){if(val!=a){good=false;break;}}else if(val!=a&&val!=b){good=false;break;}}if(good){*oy=((uint64_t)yy)&mask_n(n);*oz=((uint64_t)zz)&mask_n(n);return true;}}}return false;}
static Expr* variable_substitution(Solver*s,Expr*e){/* collect hidden vars used in e whose definitions are linear */bool any=false;size_t max=ex_maxvar(e,&any);size_t*vs=malloc((max+1)*sizeof(size_t));size_t nv=0;for(size_t v=0;v<=max;v++){Expr*d=hidden_by_var(s,v);if(d&&solver_is_linear(s,d)){/* ensure e uses v */bool used=false;/* tiny recursive membership */EV st={0};ev_push(&st,e);while(st.n){Expr*q=st.v[--st.n];if(q->k==E_VAR&&q->u.var==v){used=true;break;}if(q->k==E_NOT)ev_push(&st,q->u.unary);else if(q->k==E_SCALE)ev_push(&st,q->u.scale.e);else if(q->k>=E_AND)for(size_t i=0;i<q->u.list.n;i++)ev_push(&st,q->u.list.v[i]);}ev_free(&st);if(used)vs[nv++]=v;}}if(nv==0||nv>2){free(vs);return NULL;}VMap m={0};Expr*re=reduce_vars_rec(s->r,e,&m);Expr*zeros[2]={0};Expr*rz[2]={0};for(size_t i=0;i<nv;i++){Expr*z=ex2(s->r,E_ADD,ex_var(s->r,vs[i]),ex_neg(s->r,hidden_by_var(s,vs[i])));zeros[i]=z;rz[i]=reduce_vars_rec(s->r,z,&m);}size_t t=m.nr;if(t>10){free(vs);free(m.fwd);free(m.rev);return NULL;}size_t len=((size_t)1)<<t;uint64_t*se=truth_table(re,t,s->mask),*sz0=truth_table(rz[0],t,s->mask),*sz1=nv==2?truth_table(rz[1],t,s->mask):NULL;Expr*ret=NULL;if(nv==1){uint64_t lam;if(find_lambda(se,sz0,len,0,1,s->n,&lam)||find_lambda(se,sz0,len,-1,-2,s->n,&lam))ret=ex2(s->r,E_ADD,e,ex_neg(s->r,ex_scale(s->r,lam,zeros[0])));}else{uint64_t l0,l1;if(find_two_lambdas(se,sz0,sz1,len,0,1,s->n,&l0,&l1)||find_two_lambdas(se,sz0,sz1,len,-1,-2,s->n,&l0,&l1)){EV v={0};ev_push(&v,e);ev_push(&v,ex_neg(s->r,ex_scale(s->r,l0,zeros[0])));ev_push(&v,ex_neg(s->r,ex_scale(s->r,l1,zeros[1])));ret=ex_list(s->r,E_ADD,v.n,v.v);ev_free(&v);}}free(se);free(sz0);free(sz1);free(vs);free(m.fwd);free(m.rev);return ret;}
static Expr* is_linear_bitwise(Solver*s,Expr*l,uint64_t mask){VMap m={0};Expr*e=reduce_vars_rec(s->r,l,&m);size_t t=m.nr;if(t>10){free(m.fwd);free(m.rev);return NULL;}size_t len=((size_t)1)<<t;uint64_t*sig=truth_table(e,t,mask);bool ok=signature_bitwise(sig,len,mask);free(sig);free(m.fwd);free(m.rev);if(ok)return l;return variable_substitution(s,l);}
static Expr* make_linear(Solver*s,Expr*e,uint64_t mask,bool*ok);
/* Dynamic masks narrow local simplification only; hidden coordinates remain solver-width. */
static Expr* hide_in_var(Solver*s,Expr*e,uint64_t mask,bool*ok){if(e->k!=E_CONST){unsigned bits=(unsigned)__builtin_popcountll(mask);Expr*q=simplify_inner(s->r,e,bits,s->depth+1,ok);if(!*ok)return e;e=reduce_m(s->r,q,mask);}return hidden_intern(s,e);}
static Expr* make_bitwise(Solver*s,Expr*e,uint64_t mask,bool*ok){Rumba*r=s->r;switch(e->k){case E_CONST:{uint64_t c=e->u.c&mask;if(c==0||c==s->mask)return e;return hide_in_var(s,e,mask,ok);}case E_VAR:return e;case E_NOT:{Expr*q=make_bitwise(s,e->u.unary,mask,ok);return ex_unary(r,E_NOT,q);}case E_OR:case E_XOR:{EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,make_bitwise(s,e->u.list.v[i],mask,ok));Expr*q=ex_list(r,e->k,v.n,v.v);ev_free(&v);return q;}case E_AND:{uint64_t nm=mask;for(size_t i=0;i<e->u.list.n;i++)if(e->u.list.v[i]->k==E_CONST){uint64_t c=e->u.list.v[i]->u.c&nm;if((c&(c+1))==0)nm=c;}if(nm==0)return ex_const(r,0);EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,make_bitwise(s,e->u.list.v[i],nm,ok));Expr*q=ex_list(r,E_AND,v.n,v.v);ev_free(&v);return q;}case E_ADD:case E_SCALE:{Expr*prev=e;Expr*l=make_linear(s,e,mask,ok);if(!*ok)return e;Expr*q=is_linear_bitwise(s,l,mask);return q? q:hide_in_var(s,prev,mask,ok);}default:return hide_in_var(s,e,mask,ok);}}
static Expr* make_scaled_bitwise(Solver*s,Expr*e,uint64_t mask,bool*ok){if(e->k==E_CONST)return e;if(e->k==E_SCALE)return ex_scale(s->r,e->u.scale.c,make_bitwise(s,e->u.scale.e,mask,ok));return make_bitwise(s,e,mask,ok);}
static Expr* make_linear(Solver*s,Expr*e,uint64_t mask,bool*ok){if(e->k==E_ADD){EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,make_scaled_bitwise(s,e->u.list.v[i],mask,ok));Expr*q=ex_list(s->r,E_ADD,v.n,v.v);ev_free(&v);return q;}return make_scaled_bitwise(s,e,mask,ok);}
static Expr* make_product(Solver*s,Expr*e,bool*ok){if(e->k==E_MUL){if(e->u.list.n>s->degree)s->degree=e->u.list.n;EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,make_bitwise(s,e->u.list.v[i],s->mask,ok));Expr*q=ex_list(s->r,E_MUL,v.n,v.v);ev_free(&v);return q;}Expr*q=make_bitwise(s,e,s->mask,ok);Expr*v[1]={q};return ex_list(s->r,E_MUL,1,v);}
static Expr* make_scaled_product(Solver*s,Expr*e,bool*ok){if(e->k==E_CONST)return e;if(e->k==E_SCALE)return ex_scale(s->r,e->u.scale.c,make_product(s,e->u.scale.e,ok));return make_product(s,e,ok);}
static Expr* make_polynomial(Solver*s,Expr*e,bool*ok){if(e->k==E_ADD){EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,make_scaled_product(s,e->u.list.v[i],ok));Expr*q=ex_list(s->r,E_ADD,v.n,v.v);ev_free(&v);return q;}return make_scaled_product(s,e,ok);}
static Expr* poly_to_linear(Solver*s,Expr*e,size_t deg){Rumba*r=s->r;switch(e->k){case E_VAR:return ex_var(r,(deg-1)*s->t+e->u.var);case E_MUL:{uint64_t sign=((s->degree-e->u.list.n)&1)?UINT64_MAX:1;EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,poly_to_linear(s,e->u.list.v[i],deg+i+1));Expr*q=ex_scale(r,sign,ex_list(r,E_AND,v.n,v.v));ev_free(&v);return q;}case E_CONST:if(deg!=0)return e;return ex_const(r,((s->degree&1)?1:UINT64_MAX)*e->u.c);case E_NOT:return ex_unary(r,E_NOT,poly_to_linear(s,e->u.unary,deg));case E_SCALE:return ex_scale(r,e->u.scale.c,poly_to_linear(s,e->u.scale.e,deg));default:{EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,poly_to_linear(s,e->u.list.v[i],deg));Expr*q=ex_list(r,e->k,v.n,v.v);ev_free(&v);return q;}}}
static Expr* linear_to_poly(Solver*s,Expr*e,bool*ok){Rumba*r=s->r;if(e->k==E_AND){EV *groups=calloc(s->degree,sizeof(EV));for(size_t i=0;i<e->u.list.n;i++){Expr*t=e->u.list.v[i];if(t->k!=E_VAR){*ok=false;goto bad;}size_t d=t->u.var/s->t;if(d>=s->degree){*ok=false;goto bad;}ev_push(&groups[d],ex_var(r,t->u.var%s->t));}uint64_t sign=1;EV terms={0};for(size_t d=0;d<s->degree;d++){if(groups[d].n==0){sign*=UINT64_MAX;continue;}ev_push(&terms,ex_list(r,E_AND,groups[d].n,groups[d].v));}for(size_t d=0;d<s->degree;d++)ev_free(&groups[d]);free(groups);{Expr*q=ex_scale(r,sign,ex_list(r,E_MUL,terms.n,terms.v));ev_free(&terms);return q;}bad:for(size_t d=0;d<s->degree;d++)ev_free(&groups[d]);free(groups);return e;}if(e->k==E_ADD){EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,linear_to_poly(s,e->u.list.v[i],ok));Expr*q=ex_list(r,E_ADD,v.n,v.v);ev_free(&v);return q;}if(e->k==E_SCALE)return ex_scale(r,e->u.scale.c,linear_to_poly(s,e->u.scale.e,ok));if(e->k==E_VAR){uint64_t sign=(s->degree&1)?1:UINT64_MAX;return ex_scale(r,sign,ex_var(r,e->u.var%s->t));}if(e->k==E_CONST){uint64_t sign=(s->degree&1)?1:UINT64_MAX;return ex_scale(r,sign,e);}*ok=false;return e;}
static Expr* solve_polynomial(Solver*s,Expr*e,bool*ok){if(s->degree==1)return solve_linear(s,e,false,ok);Expr*l=poly_to_linear(s,e,0);l=solve_linear(s,l,true,ok);if(!*ok)return e;Expr*p=linear_to_poly(s,l,ok);if(!*ok)return e;return reduce_m(s->r,p,s->mask);}
static Expr* poly_to_nonpoly(Solver*s,Expr*e){if(e->k==E_VAR){Expr*d=hidden_by_var(s,e->u.var);return d?poly_to_nonpoly(s,d):e;}switch(e->k){case E_CONST:return e;case E_NOT:return ex_unary(s->r,E_NOT,poly_to_nonpoly(s,e->u.unary));case E_SCALE:return ex_scale(s->r,e->u.scale.c,poly_to_nonpoly(s,e->u.scale.e));default:{EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,poly_to_nonpoly(s,e->u.list.v[i]));Expr*q=ex_list(s->r,e->k,v.n,v.v);ev_free(&v);return q;}}}


/* semantic hidden-component merge, port of simplify/merge_hidden.rs */
static _Thread_local unsigned hidden_equality_depth = 0;
#define CARRIER_HBASE (SIZE_MAX/2)
static _Thread_local Expr *last_atom_carrier = NULL;
static _Thread_local HGKey **last_atom_keys = NULL;
static _Thread_local size_t last_atom_n = 0;

static bool tc_uses_hidden_var(Solver*s,Expr*e,size_t v){if(e->k==E_VAR)return e->u.var==v;if(e->k==E_NOT)return tc_uses_hidden_var(s,e->u.unary,v);if(e->k==E_SCALE)return tc_uses_hidden_var(s,e->u.scale.e,v);if(e->k>=E_AND)for(size_t i=0;i<e->u.list.n;i++)if(tc_uses_hidden_var(s,e->u.list.v[i],v))return true;return false;}
static int tc_keyptr_cmp_q(const void*aa,const void*bb){HGKey*a=*(HGKey*const*)aa,*b=*(HGKey*const*)bb;return hg_cmp(a,b);}
static size_t tc_key_rank(HGKey**keys,size_t n,HGKey*k){for(size_t i=0;i<n;i++)if(hg_cmp(keys[i],k)==0)return i;return SIZE_MAX;}
static Expr* tc_normalize_expr(Solver*s,Expr*e,HGKey**keys,size_t nk){
    if(e->k==E_VAR){Hidden*h=hidden_entry_by_var(s,e->u.var);if(!h)return e;size_t rank=tc_key_rank(keys,nk,h->gauge_key);assert(rank!=SIZE_MAX);return ex_var(s->r,CARRIER_HBASE+rank);}
    if(e->k==E_CONST)return e;
    if(e->k==E_NOT)return ex_unary(s->r,E_NOT,tc_normalize_expr(s,e->u.unary,keys,nk));
    if(e->k==E_SCALE)return ex_scale(s->r,e->u.scale.c,tc_normalize_expr(s,e->u.scale.e,keys,nk));
    EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,tc_normalize_expr(s,e->u.list.v[i],keys,nk));if(v.n>1)qsort(v.v,v.n,sizeof(Expr*),qcmp_exprptr);Expr*q=v.n==1?v.v[0]:ex_list(s->r,e->k,v.n,v.v);ev_free(&v);return q;
}
static void tc_capture(Solver*s,Expr*p){
    size_t nk=0;for(size_t i=0;i<s->hn;i++)if(tc_uses_hidden_var(s,p,s->h[i].var))nk++;
    HGKey**keys=nk?arena_alloc(&s->r->arena,nk*sizeof(*keys)):NULL;size_t w=0;for(size_t i=0;i<s->hn;i++)if(tc_uses_hidden_var(s,p,s->h[i].var))keys[w++]=s->h[i].gauge_key;
    if(nk>1)qsort(keys,nk,sizeof(*keys),tc_keyptr_cmp_q);
    size_t u=0;for(size_t i=0;i<nk;i++)if(i==0||hg_cmp(keys[i],keys[i-1])!=0)keys[u++]=keys[i];nk=u;
    last_atom_keys=keys;last_atom_n=nk;last_atom_carrier=tc_normalize_expr(s,p,keys,nk);
}
static bool passes_quick_zero_check(Expr*e,uint64_t mask){
    bool any=false;size_t max=ex_maxvar(e,&any);size_t nv=any?max+1:1;uint64_t*vars=calloc(nv,sizeof(uint64_t));
    for(uint64_t sample=0;sample<3;sample++){
      for(size_t i=0;i<nv;i++)vars[i]=sample==0?0:sample==1?mask:(UINT64_C(0x9e3779b97f4a7c15)+(uint64_t)i*UINT64_C(0xbf58476d1ce4e5b9))&mask;
      if((ex_eval(e,vars,nv)&mask)!=0){free(vars);return false;}
    }free(vars);return true;
}
static Expr* synth_binary(Rumba*r,Expr*l,Expr*rr,unsigned tt,uint64_t mask){switch(tt){
 case 0:return ex_const(r,0); case 1:return ex_unary(r,E_NOT,ex2(r,E_OR,l,rr)); case 2:return ex2(r,E_AND,l,ex_unary(r,E_NOT,rr)); case 3:return ex_unary(r,E_NOT,rr);
 case 4:return ex2(r,E_AND,ex_unary(r,E_NOT,l),rr); case 5:return ex_unary(r,E_NOT,l); case 6:return ex2(r,E_XOR,l,rr); case 7:return ex_unary(r,E_NOT,ex2(r,E_AND,l,rr));
 case 8:return ex2(r,E_AND,l,rr); case 9:return ex_unary(r,E_NOT,ex2(r,E_XOR,l,rr)); case 10:return l; case 11:return ex2(r,E_OR,l,ex_unary(r,E_NOT,rr));
 case 12:return rr; case 13:return ex2(r,E_OR,ex_unary(r,E_NOT,l),rr); case 14:return ex2(r,E_OR,l,rr); case 15:return ex_const(r,mask); }
 return ex_const(r,0);
}
static size_t infer_binary_tables(const uint64_t*target,const uint64_t*left,const uint64_t*right,size_t ns,unsigned n,unsigned out[16]){
    int obs[4]={-1,-1,-1,-1};
    for(size_t sidx=0;sidx<ns;sidx++)for(unsigned bit=0;bit<n;bit++){
      unsigned in=(unsigned)((left[sidx]>>bit)&1)|((unsigned)((right[sidx]>>bit)&1)<<1);int o=(int)((target[sidx]>>bit)&1);
      if(obs[in]>=0&&obs[in]!=o)return 0;
      obs[in]=o;
    }
    size_t no=0;for(unsigned tt=0;tt<16;tt++){bool good=true;for(unsigned in=0;in<4;in++)if(obs[in]>=0&&(int)((tt>>in)&1)!=obs[in]){good=false;break;}if(good)out[no++]=tt;}return no;
}
typedef struct { uint64_t **vals; size_t count,len; } SampleSet;
static void samples_free(SampleSet*x){if(!x)return;for(size_t i=0;i<x->count;i++)free(x->vals[i]);free(x->vals);memset(x,0,sizeof *x);}
static bool make_signature_samples(Solver*s,Expr**es,size_t count,SampleSet*out){
    VMap m={0};Expr**red=calloc(count,sizeof(*red));for(size_t i=0;i<count;i++)red[i]=reduce_vars_rec(s->r,es[i],&m);if(m.nr>10){free(red);free(m.fwd);free(m.rev);return false;}
    size_t base=((size_t)1)<<m.nr,len=base+3;uint64_t**vals=calloc(count,sizeof(*vals));for(size_t i=0;i<count;i++){vals[i]=malloc(len*sizeof(uint64_t));uint64_t*tt=truth_table(red[i],m.nr,s->mask);memcpy(vals[i],tt,base*sizeof(uint64_t));free(tt);}
    for(uint64_t sample=0;sample<3;sample++){uint64_t*vars=calloc(m.nr?m.nr:1,sizeof(uint64_t));for(size_t v=0;v<m.nr;v++)vars[v]=(UINT64_C(0x9e3779b97f4a7c15)*(sample+1)+UINT64_C(0xbf58476d1ce4e5b9)*(v+1))&s->mask;for(size_t i=0;i<count;i++)vals[i][base+sample]=ex_eval(red[i],vars,m.nr)&s->mask;free(vars);}
    free(red);free(m.fwd);free(m.rev);*out=(SampleSet){vals,count,len};return true;
}
static bool prove_hidden_relation(Solver*s,Expr*left,Expr*right){
    Expr*diff=ex2(s->r,E_ADD,left,ex_neg(s->r,right));
    diff=reduce_m(s->r,poly_to_nonpoly(s,diff),s->mask);if(!passes_quick_zero_check(diff,s->mask))return false;
    hidden_equality_depth++;bool any=false;size_t maxv=ex_maxvar(diff,&any);bool ok=true;Solver sub={.r=s->r,.n=s->n,.mask=s->mask,.t=any?maxv+1:1,.degree=1,.depth=s->depth+1};Expr*q=solver_solve(&sub,diff,&ok);bool zero=ok&&q->k==E_CONST&&((q->u.c&s->mask)==0);free(sub.h);hidden_equality_depth--;return zero;
}
typedef struct {size_t var;Expr*alias;} Alias;
static Expr* replace_aliases_rec(Rumba*r,Expr*e,Alias*a,size_t na){if(e->k==E_VAR){for(size_t i=0;i<na;i++)if(a[i].var==e->u.var)return replace_aliases_rec(r,a[i].alias,a,na);return e;}switch(e->k){case E_CONST:return e;case E_NOT:return ex_unary(r,E_NOT,replace_aliases_rec(r,e->u.unary,a,na));case E_SCALE:return ex_scale(r,e->u.scale.c,replace_aliases_rec(r,e->u.scale.e,a,na));default:{EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,replace_aliases_rec(r,e->u.list.v[i],a,na));Expr*q=ex_list(r,e->k,v.n,v.v);ev_free(&v);return q;}}}
static bool expr_uses_var(Expr*e,size_t v){if(e->k==E_VAR)return e->u.var==v;if(e->k==E_NOT)return expr_uses_var(e->u.unary,v);if(e->k==E_SCALE)return expr_uses_var(e->u.scale.e,v);if(e->k>=E_AND)for(size_t i=0;i<e->u.list.n;i++)if(expr_uses_var(e->u.list.v[i],v))return true;return false;}
typedef struct {Expr*e;size_t size;} Candidate;
static int cand_cmp(const void*aa,const void*bb){const Candidate*a=aa,*b=bb;if(a->size!=b->size)return a->size<b->size?-1:1;return ex_cmp(a->e,b->e);}
static Expr* merge_equal_hidden_components(Solver*s,Expr*root,bool*changed){
    *changed=false;if(hidden_equality_depth||s->hn==0)return root;
    /* non-constant components */ size_t nc=0;for(size_t i=0;i<s->hn;i++)if(s->h[i].def->k!=E_CONST)nc++;if(!nc)return root;
    size_t*ci=malloc(nc*sizeof(size_t));size_t cp=0;for(size_t i=0;i<s->hn;i++)if(s->h[i].def->k!=E_CONST)ci[cp++]=i;
    /* visible variables */ bool*visible=NULL;size_t viscap=0;for(size_t ii=0;ii<nc;ii++){Expr*d=s->h[ci[ii]].def;bool any=false;size_t mx=ex_maxvar(d,&any);if(any&&mx+1>viscap){size_t old=viscap;viscap=mx+1;visible=realloc(visible,viscap);memset(visible+old,0,viscap-old);}for(size_t v=0;v<=mx&&any;v++)if(expr_uses_var(d,v)&&!hidden_by_var(s,v))visible[v]=true;}
    size_t nv=0;for(size_t v=0;v<viscap;v++)if(visible[v])nv++;
    size_t natoms=nc+nv,total=nc+natoms;Expr**sample_expr=calloc(total,sizeof(Expr*));Expr**atom_expr=calloc(natoms,sizeof(Expr*));size_t*atom_var=calloc(natoms,sizeof(size_t));bool*atom_hidden=calloc(natoms,sizeof(bool));
    for(size_t i=0;i<nc;i++)sample_expr[i]=poly_to_nonpoly(s,s->h[ci[i]].def);
    size_t ap=0;for(size_t i=0;i<nc;i++){atom_expr[ap]=ex_var(s->r,s->h[ci[i]].var);atom_var[ap]=s->h[ci[i]].var;atom_hidden[ap]=true;sample_expr[nc+ap]=poly_to_nonpoly(s,s->h[ci[i]].def);ap++;}
    for(size_t v=0;v<viscap;v++)if(visible[v]){atom_expr[ap]=ex_var(s->r,v);atom_var[ap]=v;atom_hidden[ap]=false;sample_expr[nc+ap]=ex_var(s->r,v);ap++;}
    SampleSet ss={0};if(!make_signature_samples(s,sample_expr,total,&ss)){free(ci);free(visible);free(sample_expr);free(atom_expr);free(atom_var);free(atom_hidden);return root;}
    Alias*aliases=NULL;size_t na=0,acap=0;
    for(size_t ti=0;ti<nc;ti++){
      size_t target_var=s->h[ci[ti]].var;Candidate*cands=NULL;size_t cn=0,ccap=0;
      #define ADDCAND(X) do{if(cn==ccap){ccap=ccap?ccap*2:32;cands=realloc(cands,ccap*sizeof(*cands));}Expr*_ce=(X);cands[cn++]=(Candidate){_ce,ex_size(_ce)};}while(0)
      unsigned tabs[16];size_t nt;
      for(size_t li=0;li<natoms;li++){if(atom_hidden[li]&&atom_var[li]>=target_var)continue;for(size_t ri=li+1;ri<natoms;ri++){if(atom_hidden[ri]&&atom_var[ri]>=target_var)continue;nt=infer_binary_tables(ss.vals[ti],ss.vals[nc+li],ss.vals[nc+ri],ss.len,s->n,tabs);for(size_t k=0;k<nt;k++)ADDCAND(synth_binary(s->r,atom_expr[li],atom_expr[ri],tabs[k],s->mask));}}
      if(cn>1)qsort(cands,cn,sizeof(*cands),cand_cmp);
      size_t w=0;for(size_t i=0;i<cn;i++)if(i==0||!ex_eq(cands[i].e,cands[i-1].e))cands[w++]=cands[i];cn=w;
      for(size_t i=0;i<cn;i++)if(prove_hidden_relation(s,ex_var(s->r,target_var),cands[i].e)){if(na==acap){acap=acap?acap*2:8;aliases=realloc(aliases,acap*sizeof(*aliases));}aliases[na++]=(Alias){target_var,cands[i].e};break;}
      free(cands);
      #undef ADDCAND
    }
    samples_free(&ss);free(ci);free(visible);free(sample_expr);free(atom_expr);free(atom_var);free(atom_hidden);
    if(na){*changed=true;root=reduce_m(s->r,replace_aliases_rec(s->r,root,aliases,na),s->mask);}free(aliases);return root;
}

/* Hidden Cut: contextual quotient, port of simplify/hidden_cut.rs. */
typedef struct { size_t *v,n,cap; } Monomial;
typedef struct { Monomial m; uint64_t c; } HCTerm;
typedef struct { HCTerm *v; size_t n,cap; } Terms;
typedef struct { Monomial pivot; Terms terms; } HCRule;
typedef struct { HCRule *v; size_t n,cap; } HCRules;
typedef struct { Expr *core; uint64_t c; } HCCoeff;
typedef struct { HCCoeff *v; size_t n,cap; } HCCoeffs;
typedef struct { size_t var; bool complemented; } HCLiteral;
typedef struct { HCLiteral lit; Expr *def; } HCLitEntry;
typedef struct { size_t var; Expr *def; bool hidden; } HCDef;
typedef struct { HCDef *v; size_t n,cap; } HCDefs;

static void mono_free(Monomial*m){free(m->v);memset(m,0,sizeof *m);} 
static Monomial mono_clone(const Monomial*m){Monomial q={0};if(m->n){q.v=malloc(m->n*sizeof(size_t));memcpy(q.v,m->v,m->n*sizeof(size_t));q.n=q.cap=m->n;}return q;}
static void mono_push(Monomial*m,size_t x){if(m->n==m->cap){m->cap=m->cap?m->cap*2:4;m->v=realloc(m->v,m->cap*sizeof(size_t));}m->v[m->n++]=x;}
static int mono_cmp(const Monomial*a,const Monomial*b){size_t n=a->n<b->n?a->n:b->n;for(size_t i=0;i<n;i++){int c=cmp_sz(a->v[i],b->v[i]);if(c)return c;}return cmp_sz(a->n,b->n);}
static bool mono_eq(const Monomial*a,const Monomial*b){return mono_cmp(a,b)==0;}
static bool mono_subset(const Monomial*a,const Monomial*b){size_t i=0,j=0;while(i<a->n&&j<b->n){if(a->v[i]==b->v[j]){i++;j++;}else if(a->v[i]>b->v[j])j++;else return false;}return i==a->n;}
static Monomial mono_union(const Monomial*a,const Monomial*b){Monomial q={0};size_t i=0,j=0;while(i<a->n||j<b->n){size_t x;if(j==b->n||(i<a->n&&a->v[i]<b->v[j]))x=a->v[i++];else if(i==a->n||b->v[j]<a->v[i])x=b->v[j++];else{x=a->v[i];i++;j++;}mono_push(&q,x);}return q;}
static Monomial mono_diff(const Monomial*a,const Monomial*b){Monomial q={0};size_t j=0;for(size_t i=0;i<a->n;i++){while(j<b->n&&b->v[j]<a->v[i])j++;if(j>=b->n||b->v[j]!=a->v[i])mono_push(&q,a->v[i]);}return q;}
static int size_t_cmp_q(const void*aa,const void*bb){size_t a=*(const size_t*)aa,b=*(const size_t*)bb;return cmp_sz(a,b);}
static bool mono_from_expr(Expr*e,Monomial*out){*out=(Monomial){0};if(e->k==E_CONST&&e->u.c==1)return true;if(e->k==E_VAR){mono_push(out,e->u.var);return true;}if(e->k==E_AND){for(size_t i=0;i<e->u.list.n;i++){Expr*x=e->u.list.v[i];if(x->k!=E_VAR){mono_free(out);return false;}mono_push(out,x->u.var);}if(out->n>1)qsort(out->v,out->n,sizeof(size_t),size_t_cmp_q);size_t w=0;for(size_t i=0;i<out->n;i++)if(i==0||out->v[i]!=out->v[i-1])out->v[w++]=out->v[i];out->n=w;return true;}return false;}

static void terms_free(Terms*t){for(size_t i=0;i<t->n;i++)mono_free(&t->v[i].m);free(t->v);memset(t,0,sizeof *t);} 
static ssize_t terms_find(const Terms*t,const Monomial*m){for(size_t i=0;i<t->n;i++)if(mono_eq(&t->v[i].m,m))return (ssize_t)i;return -1;}
static void terms_set(Terms*t,const Monomial*m,uint64_t c){ssize_t k=terms_find(t,m);if(c==0){if(k>=0){mono_free(&t->v[k].m);memmove(&t->v[k],&t->v[k+1],(t->n-(size_t)k-1)*sizeof(*t->v));t->n--;}return;}if(k>=0){t->v[k].c=c;return;}if(t->n==t->cap){t->cap=t->cap?t->cap*2:8;t->v=realloc(t->v,t->cap*sizeof(*t->v));}t->v[t->n++]=(HCTerm){mono_clone(m),c};}
static Terms terms_clone(const Terms*t){Terms q={0};for(size_t i=0;i<t->n;i++)terms_set(&q,&t->v[i].m,t->v[i].c);return q;}
static int term_cmp_q(const void*aa,const void*bb){const HCTerm*a=aa,*b=bb;return mono_cmp(&a->m,&b->m);} 
static void terms_sort(Terms*t){if(t->n>1)qsort(t->v,t->n,sizeof(*t->v),term_cmp_q);} 
static bool terms_has_superset(const Terms*t,const Monomial*m){for(size_t i=0;i<t->n;i++)if(mono_subset(m,&t->v[i].m))return true;return false;}
static int terms_cmp(const Terms*a,const Terms*b){size_t n=a->n<b->n?a->n:b->n;for(size_t i=0;i<n;i++){int c=mono_cmp(&a->v[i].m,&b->v[i].m);if(c)return c;c=cmp_u64(a->v[i].c,b->v[i].c);if(c)return c;}return cmp_sz(a->n,b->n);}

static void coeffs_free(HCCoeffs*c){free(c->v);memset(c,0,sizeof *c);} 
static void coeff_add(HCCoeffs*c,Expr*core,uint64_t x,uint64_t mask){size_t i;for(i=0;i<c->n;i++)if(ex_eq(c->v[i].core,core))break;if(i==c->n){if(c->n==c->cap){c->cap=c->cap?c->cap*2:8;c->v=realloc(c->v,c->cap*sizeof(*c->v));}c->v[c->n++]=(HCCoeff){core,0};}c->v[i].c=(c->v[i].c+x)&mask;}
static int coeff_cmp_q(const void*aa,const void*bb){const HCCoeff*a=aa,*b=bb;return ex_cmp(a->core,b->core);} 
static HCCoeffs hc_coeffs(Rumba*r,Expr*e,uint64_t mask){HCCoeffs out={0};size_t n=(e->k==E_ADD)?e->u.list.n:1;for(size_t i=0;i<n;i++){Expr*t=(e->k==E_ADD)?e->u.list.v[i]:e;uint64_t c=1;Expr*core=t;if(t->k==E_SCALE){c=t->u.scale.c&mask;core=t->u.scale.e;}else if(t->k==E_CONST){c=t->u.c&mask;core=ex_const(r,1);}coeff_add(&out,core,c,mask);}size_t w=0;for(size_t i=0;i<out.n;i++)if(out.v[i].c)out.v[w++]=out.v[i];out.n=w;if(out.n>1)qsort(out.v,out.n,sizeof(*out.v),coeff_cmp_q);return out;}
static Expr* hc_arithmetic(Solver*s,Expr*e){if(e->k==E_NOT){Expr*sum=ex2(s->r,E_ADD,ex_neg(s->r,e->u.unary),ex_const(s->r,UINT64_MAX));return reduce_m(s->r,sum,s->mask);}return e;}
static uint64_t hc_odd_inverse(uint64_t c,uint64_t mask){c&=mask;uint64_t inv=c;for(int i=0;i<5;i++)inv=inv*(2-c*inv)&mask;return inv;}
static bool hc_scale_relation(Solver*s,const HCCoeffs*a,Expr*base,uint64_t*outk){Expr*arith=hc_arithmetic(s,base);HCCoeffs b=hc_coeffs(s->r,arith,s->mask);if(a->n!=b.n){coeffs_free(&b);return false;}for(size_t i=0;i<a->n;i++)if(!ex_eq(a->v[i].core,b.v[i].core)){coeffs_free(&b);return false;}size_t pivot=SIZE_MAX;for(size_t i=0;i<b.n;i++)if(b.v[i].c&1){pivot=i;break;}if(pivot==SIZE_MAX){coeffs_free(&b);return false;}uint64_t k=a->v[pivot].c*hc_odd_inverse(b.v[pivot].c,s->mask)&s->mask;for(size_t i=0;i<b.n;i++)if(a->v[i].c!=(b.v[i].c*k&s->mask)){coeffs_free(&b);return false;}coeffs_free(&b);*outk=k;return true;}
static bool hc_even_nonconstant(Solver*s,Expr*e){e=reduce_m(s->r,e,s->mask);size_t n=e->k==E_ADD?e->u.list.n:1;for(size_t i=0;i<n;i++){Expr*t=e->k==E_ADD?e->u.list.v[i]:e;if(t->k==E_CONST)continue;if(t->k==E_SCALE&&((t->u.scale.c&1)==0))continue;return false;}return true;}
static Expr* hc_addc(Solver*s,Expr*e,uint64_t c){return reduce_m(s->r,ex2(s->r,E_ADD,e,ex_const(s->r,c&s->mask)),s->mask);} 
static Expr* hc_neg(Solver*s,Expr*e){return reduce_m(s->r,ex_neg(s->r,e),s->mask);} 

static bool hc_term_map(Solver*s,Expr*e,Terms*out){*out=(Terms){0};e=reduce_m(s->r,e,s->mask);HCCoeffs cs=hc_coeffs(s->r,e,s->mask);for(size_t i=0;i<cs.n;i++){Monomial m={0};if(!mono_from_expr(cs.v[i].core,&m)){mono_free(&m);coeffs_free(&cs);terms_free(out);return false;}uint64_t c=m.n?cs.v[i].c:(0-cs.v[i].c)&s->mask;ssize_t k=terms_find(out,&m);uint64_t old=k>=0?out->v[k].c:0;terms_set(out,&m,(old+c)&s->mask);mono_free(&m);}coeffs_free(&cs);terms_sort(out);return true;}
static Expr* hc_build(Solver*s,const Terms*t){EV out={0};for(size_t i=0;i<t->n;i++){const Monomial*m=&t->v[i].m;uint64_t c=t->v[i].c;if(m->n==0){ev_push(&out,ex_const(s->r,(0-c)&s->mask));continue;}EV xs={0};for(size_t j=0;j<m->n;j++)ev_push(&xs,ex_var(s->r,m->v[j]));Expr*and=ex_list(s->r,E_AND,xs.n,xs.v);ev_free(&xs);ev_push(&out,ex_scale(s->r,c,and));}Expr*e=ex_list(s->r,E_ADD,out.n,out.v);ev_free(&out);return reduce_m(s->r,e,s->mask);}
static size_t hc_hidden_rank(Solver*s,const Monomial*m){size_t c=0;for(size_t i=0;i<m->n;i++)if(hidden_by_var(s,m->v[i]))c++;return c;}
static int hc_rank_cmp(Solver*s,const Monomial*a,const Monomial*b){size_t ah=hc_hidden_rank(s,a),bh=hc_hidden_rank(s,b);if(ah!=bh)return ah<bh?-1:1;if(a->n!=b->n)return a->n<b->n?-1:1;return mono_cmp(a,b);}
static bool hc_normalize_rule(Solver*s,Expr*rel,const Terms*root,HCRule*out){Terms ts={0};if(!hc_term_map(s,rel,&ts))return false;ssize_t best=-1;for(size_t i=0;i<ts.n;i++){Monomial*m=&ts.v[i].m;if(m->n==0||!(ts.v[i].c&1))continue;bool admissible=true;for(size_t j=0;j<ts.n;j++)if(i!=j&&mono_subset(m,&ts.v[j].m)){admissible=false;break;}if(!admissible)continue;if(best<0||hc_rank_cmp(s,m,&ts.v[best].m)>0)best=(ssize_t)i;}if(best<0||!terms_has_superset(root,&ts.v[best].m)){terms_free(&ts);return false;}uint64_t inv=hc_odd_inverse(ts.v[best].c,s->mask);for(size_t i=0;i<ts.n;i++)ts.v[i].c=ts.v[i].c*inv&s->mask;*out=(HCRule){mono_clone(&ts.v[best].m),ts};return true;}
static void hc_rule_free(HCRule*r){mono_free(&r->pivot);terms_free(&r->terms);} 
static void hc_rules_free(HCRules*r){for(size_t i=0;i<r->n;i++)hc_rule_free(&r->v[i]);free(r->v);memset(r,0,sizeof *r);} 
static void hc_consider(Solver*s,HCRules*rs,Expr*rel,const Terms*root){HCRule q={0};if(!hc_normalize_rule(s,rel,root,&q))return;if(rs->n==rs->cap){rs->cap=rs->cap?rs->cap*2:8;rs->v=realloc(rs->v,rs->cap*sizeof(*rs->v));}rs->v[rs->n++]=q;}
static Expr* hc_apply_rule(Solver*s,const Terms*root,const HCRule*r){Terms out=terms_clone(root);for(size_t i=0;i<root->n;i++){const Monomial*m=&root->v[i].m;uint64_t c=root->v[i].c;if(!mono_subset(&r->pivot,m))continue;terms_set(&out,m,0);Monomial ctx=mono_diff(m,&r->pivot);for(size_t j=0;j<r->terms.n;j++){const HCTerm*rt=&r->terms.v[j];if(mono_eq(&rt->m,&r->pivot))continue;Monomial nm=mono_union(&ctx,&rt->m);ssize_t k=terms_find(&out,&nm);uint64_t old=k>=0?out.v[k].c:0;uint64_t nv=(old-c*rt->c)&s->mask;terms_set(&out,&nm,nv);mono_free(&nm);}mono_free(&ctx);}terms_sort(&out);Expr*e=hc_build(s,&out);terms_free(&out);return e;}
static int hc_rule_cmp(Solver*s,const HCRule*a,const HCRule*b){int c=hc_rank_cmp(s,&a->pivot,&b->pivot);if(c)return c;return terms_cmp(&a->terms,&b->terms);}
static Expr* hc_choose_rule(Solver*s,const Terms*root,HCRules*rs){Expr*best=NULL;size_t bestn=SIZE_MAX;ssize_t bi=-1;for(size_t i=0;i<rs->n;i++){Expr*e=hc_apply_rule(s,root,&rs->v[i]);Terms t={0};size_t n=hc_term_map(s,e,&t)?t.n:SIZE_MAX;terms_free(&t);if(!best||n<bestn||(n==bestn&&hc_rule_cmp(s,&rs->v[i],&rs->v[bi])>0)){best=e;bestn=n;bi=(ssize_t)i;}}return best;}

static Expr* hc_known(Solver*s,Expr*e){size_t v;if(hidden_find_expr(s,e,&v))return ex_var(s->r,v);Expr*c=complement_expr(s->r,e,s->mask);if(hidden_find_expr(s,c,&v))return reduce_m(s->r,ex_unary(s->r,E_NOT,ex_var(s->r,v)),s->mask);return NULL;}
static Expr* hc_fold_known(Solver*s,Expr*e){Expr*q=e;switch(e->k){case E_VAR:case E_CONST:break;case E_NOT:q=ex_unary(s->r,E_NOT,hc_fold_known(s,e->u.unary));break;case E_SCALE:q=ex_scale(s->r,e->u.scale.c,hc_fold_known(s,e->u.scale.e));break;default:{EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,hc_fold_known(s,e->u.list.v[i]));q=ex_list(s->r,e->k,v.n,v.v);ev_free(&v);break;}}q=reduce_m(s->r,q,s->mask);Expr*k=hc_known(s,q);return k?k:q;}
static Expr* hc_bitwise_view(Solver*s,Expr*e){e=reduce_m(s->r,e,s->mask);Expr*k=hc_known(s,e);if(k)return k;if(solver_is_linear(s,e)){Expr*q=is_linear_bitwise(s,e,s->mask);if(q)return reduce_m(s->r,q,s->mask);}return NULL;}
static Expr* hc_bitwise_view_refolded(Solver*s,Expr*e){e=reduce_m(s->r,e,s->mask);Expr*q=hc_bitwise_view(s,e);if(q)return q;return hc_bitwise_view(s,hc_fold_known(s,e));}
static Expr* hc_certify_free(Solver*s,Expr*e){bool ok=true;Expr*q=solve_linear(s,reduce_m(s->r,e,s->mask),false,&ok);return ok?reduce_m(s->r,q,s->mask):NULL;}
/* Symbolic ObservedEq authority: observer & lhs == observer & rhs. Producers nominate; this path proves/lowers it fail-closed. */
static Expr* hc_lower_observed_eq(Solver*s,Expr*observer,Expr*lhs,Expr*rhs){Expr*l=ex2(s->r,E_AND,observer,lhs);Expr*r=ex2(s->r,E_AND,observer,rhs);return hc_certify_free(s,ex2(s->r,E_ADD,l,ex_neg(s->r,r)));}
static void hc_emit_observed_eq(Solver*s,Expr*observer,Expr*lhs,Expr*rhs,const Terms*root,HCRules*rules){Expr*rel=hc_lower_observed_eq(s,observer,lhs,rhs);if(rel)hc_consider(s,rules,rel,root);}

static void hc_defs_push(HCDefs*d,size_t var,Expr*e,bool hidden){for(size_t i=0;i<d->n;i++)if(d->v[i].var==var)return;if(d->n==d->cap){d->cap=d->cap?d->cap*2:8;d->v=realloc(d->v,d->cap*sizeof(*d->v));}d->v[d->n++]=(HCDef){var,e,hidden};}
static int hc_def_cmp_q(const void*aa,const void*bb){const HCDef*a=aa,*b=bb;return cmp_sz(a->var,b->var);} 
static HCDef* hc_def_get(HCDefs*d,size_t var){for(size_t i=0;i<d->n;i++)if(d->v[i].var==var)return &d->v[i];return NULL;}
static void hc_collect_vars_expr(Expr*e,size_t**vs,size_t*n,size_t*cap){if(e->k==E_VAR){for(size_t i=0;i<*n;i++)if((*vs)[i]==e->u.var)return;if(*n==*cap){*cap=*cap?*cap*2:8;*vs=realloc(*vs,*cap*sizeof(size_t));}(*vs)[(*n)++]=e->u.var;return;}if(e->k==E_NOT)hc_collect_vars_expr(e->u.unary,vs,n,cap);else if(e->k==E_SCALE)hc_collect_vars_expr(e->u.scale.e,vs,n,cap);else if(e->k>=E_AND)for(size_t i=0;i<e->u.list.n;i++)hc_collect_vars_expr(e->u.list.v[i],vs,n,cap);}
static HCDefs hc_definitions(Solver*s,Expr*root){HCDefs d={0};for(size_t i=0;i<s->hn;i++)hc_defs_push(&d,s->h[i].var,reduce_m(s->r,s->h[i].def,s->mask),true);size_t*vs=NULL,n=0,cap=0;hc_collect_vars_expr(root,&vs,&n,&cap);for(size_t i=0;i<s->hn;i++)hc_collect_vars_expr(s->h[i].def,&vs,&n,&cap);for(size_t i=0;i<n;i++)if(!hc_def_get(&d,vs[i]))hc_defs_push(&d,vs[i],ex_var(s->r,vs[i]),false);free(vs);if(d.n>1)qsort(d.v,d.n,sizeof(*d.v),hc_def_cmp_q);return d;}
static Expr* hc_literal_expr(Solver*s,HCLiteral l){Expr*e=ex_var(s->r,l.var);return l.complemented?reduce_m(s->r,ex_unary(s->r,E_NOT,e),s->mask):e;}
static Expr* hc_literal_def(Solver*s,HCDefs*d,HCLiteral l){HCDef*q=hc_def_get(d,l.var);if(!q)return NULL;return l.complemented?complement_expr(s->r,q->def,s->mask):q->def;}
static int hc_lit_cmp(HCLiteral a,HCLiteral b){if(a.var!=b.var)return a.var<b.var?-1:1;return a.complemented==b.complemented?0:(a.complemented?1:-1);}
static HCLitEntry* hc_literals(Solver*s,HCDefs*d,size_t*outn){size_t cap=d->n+s->hn,n=0;HCLitEntry*a=malloc((cap?cap:1)*sizeof(*a));for(size_t i=0;i<d->n;i++){HCLiteral direct={d->v[i].var,false};a[n++]=(HCLitEntry){direct,d->v[i].def};if(d->v[i].hidden){HCLiteral c={d->v[i].var,true};a[n++]=(HCLitEntry){c,hc_literal_def(s,d,c)};}}*outn=n;return a;}
static bool hc_root_has_mono_plus(const Terms*root,const Monomial*small,size_t v){Monomial one={0};mono_push(&one,v);Monomial big=mono_union(small,&one);mono_free(&one);bool yes=terms_find(root,&big)>=0;mono_free(&big);return yes;}

static void hc_collect_valuation(Solver*s,Expr*root,const Terms*rt,HCDefs*defs,HCLitEntry*lits,size_t nl,HCRules*rules){size_t*rv=NULL,rn=0,rc=0;hc_collect_vars_expr(root,&rv,&rn,&rc);if(rn>1){for(size_t i=0;i<rn;i++)for(size_t j=i+1;j<rn;j++)if(rv[j]<rv[i]){size_t z=rv[i];rv[i]=rv[j];rv[j]=z;}}for(size_t yi=0;yi<rn;yi++){size_t y=rv[yi];HCDef*yd=hc_def_get(defs,y);if(!yd||!hc_even_nonconstant(s,yd->def))continue;for(int pred=0;pred<2;pred++){Expr*candidate=pred?hc_addc(s,yd->def,1):yd->def;HCCoeffs cc=hc_coeffs(s->r,hc_arithmetic(s,candidate),s->mask);/* one best representative per var */HCLitEntry**best=calloc(defs->n?defs->n:1,sizeof(*best));for(size_t li=0;li<nl;li++){uint64_t k;if(!hc_scale_relation(s,&cc,lits[li].def,&k)||((k&1)!=0))continue;size_t slot=SIZE_MAX;for(size_t di=0;di<defs->n;di++)if(defs->v[di].var==lits[li].lit.var){slot=di;break;}if(slot==SIZE_MAX)continue;if(!best[slot]||hc_lit_cmp(lits[li].lit,best[slot]->lit)<0)best[slot]=&lits[li];}for(size_t di=0;di<defs->n;di++)if(best[di]){HCLitEntry*base=best[di];Expr*predv=hc_bitwise_view_refolded(s,hc_addc(s,base->def,s->mask));if(!predv)continue;Expr*observer=pred?reduce_m(s->r,ex_unary(s->r,E_NOT,ex_var(s->r,y)),s->mask):ex_var(s->r,y);hc_emit_observed_eq(s,observer,hc_literal_expr(s,base->lit),predv,rt,rules);}free(best);coeffs_free(&cc);}}free(rv);}
static void hc_collect_subset(Solver*s,const Terms*rt,HCDefs*defs,HCLitEntry*lits,size_t nl,HCRules*rules){for(size_t si=0;si<rt->n;si++){const Monomial*small=&rt->v[si].m;for(size_t xi=0;xi<small->n;xi++){size_t x=small->v[xi];HCDef*xd=hc_def_get(defs,x);if(!xd)continue;Expr*want=hc_neg(s,xd->def);HCLitEntry*partner=NULL;for(size_t li=0;li<nl;li++){if(!ex_eq(lits[li].def,want)||!hc_root_has_mono_plus(rt,small,lits[li].lit.var))continue;if(!partner||hc_lit_cmp(lits[li].lit,partner->lit)<0)partner=&lits[li];}if(!partner)continue;for(size_t zi=0;zi<small->n;zi++){size_t z=small->v[zi];if(!hidden_by_var(s,z))continue;HCDef*zd=hc_def_get(defs,z);if(!zd)continue;Expr*b=hc_bitwise_view_refolded(s,hc_neg(s,zd->def));if(!b)continue;Expr*observer=ex_var(s->r,x);Expr*rel=hc_lower_observed_eq(s,observer,b,observer);if(!rel||!(rel->k==E_CONST&&((rel->u.c&s->mask)==0)))continue;Expr*lhs=ex2(s->r,E_AND,ex_var(s->r,z),hc_literal_expr(s,partner->lit));hc_emit_observed_eq(s,observer,lhs,ex_var(s->r,z),rt,rules);}}}}
static Expr* hidden_cut_close(Solver*s,Expr*root){Terms rt={0};if(!hc_term_map(s,root,&rt))return root;HCDefs defs=hc_definitions(s,root);size_t nl=0;HCLitEntry*lits=hc_literals(s,&defs,&nl);HCRules rules={0};hc_collect_valuation(s,root,&rt,&defs,lits,nl,&rules);hc_collect_subset(s,&rt,&defs,lits,nl,&rules);Expr*out=hc_choose_rule(s,&rt,&rules);if(!out)out=root;hc_rules_free(&rules);terms_free(&rt);free(defs.v);free(lits);return out;}


static Expr* solver_solve(Solver*s,Expr*e,bool*ok){e=reduce_m(s->r,e,s->mask);Expr*p=make_polynomial(s,e,ok);if(!*ok)return e;size_t first_degree=s->degree;bool merged=false;p=merge_equal_hidden_components(s,p,&merged);if(merged&&first_degree>1){s->degree=1;p=make_polynomial(s,p,ok);if(!*ok)return e;}else s->degree=first_degree;p=solve_polynomial(s,p,ok);if(!*ok)return e;if(s->hn)p=hidden_cut_close(s,p);if(s->depth==0&&hidden_equality_depth==0)tc_capture(s,p);if(s->hn){p=poly_to_nonpoly(s,p);p=reduce_m(s->r,p,s->mask);}return p;}
static Expr* simplify_inner(Rumba*r,Expr*e,unsigned n,unsigned depth,bool*ok){if(depth>32){*ok=false;return e;}bool any=false;size_t maxv=ex_maxvar(e,&any);Solver s={.r=r,.n=n,.mask=mask_n(n),.t=any?maxv+1:1,.degree=1,.depth=depth};Expr*q=solver_solve(&s,e,ok);free(s.h);return q;}

/* cosmetic prettify */
static Expr* peel(Expr*e){while((e->k>=E_AND&&e->k<=E_MUL)&&e->u.list.n==1)e=e->u.list.v[0];return e;}
static void scaled_term(Expr*e,uint64_t mask,uint64_t*c,Expr**core){e=peel(e);if(e->k==E_SCALE){*c=e->u.scale.c&mask;*core=peel(e->u.scale.e);}else{*c=1;*core=e;}}
static Expr* scale_pretty(Rumba*r,uint64_t c,Expr*e,uint64_t mask){c&=mask;return c==0?ex_const(r,0):c==1?e:ex_scale(r,c,e);}
static Expr* assoc2(Rumba*r,Kind k,Expr*a,Expr*b){EV v={0};if(a->k==k)for(size_t i=0;i<a->u.list.n;i++)ev_push(&v,a->u.list.v[i]);else ev_push(&v,a);if(b->k==k)for(size_t i=0;i<b->u.list.n;i++)ev_push(&v,b->u.list.v[i]);else ev_push(&v,b);Expr*out=ex_list(r,k,v.n,v.v);ev_free(&v);return out;}
static Expr* not_smaller(Rumba*r,Expr*x){Expr*orig=ex_unary(r,E_NOT,x);if(x->k!=E_AND&&x->k!=E_OR)return orig;EV v={0};for(size_t i=0;i<x->u.list.n;i++){Expr*q=peel(x->u.list.v[i]);ev_push(&v,q->k==E_NOT?peel(q->u.unary):ex_unary(r,E_NOT,q));}Expr*cand=ex_list(r,x->k==E_AND?E_OR:E_AND,v.n,v.v);ev_free(&v);return ex_size(cand)<ex_size(orig)?cand:orig;}
static size_t conj_n(Expr*e){e=peel(e);return e->k==E_AND?e->u.list.n:1;}
static Expr* conj_at(Expr*e,size_t i){e=peel(e);return e->k==E_AND?peel(e->u.list.v[i]):e;}
static bool conj_has(Expr*e,Expr*f){for(size_t i=0;i<conj_n(e);i++)if(ex_eq(conj_at(e,i),f))return true;return false;}
static bool conj_union_eq(Expr*z,Expr*x,Expr*y){size_t nx=conj_n(x),ny=conj_n(y),common=0;for(size_t i=0;i<nx;i++)if(conj_has(y,conj_at(x,i)))common++;if(conj_n(z)!=nx+ny-common)return false;for(size_t i=0;i<nx;i++)if(!conj_has(z,conj_at(x,i)))return false;for(size_t i=0;i<ny;i++)if(!conj_has(z,conj_at(y,i)))return false;return true;}
static Expr* factor_join(Rumba*r,Kind op,Expr*x,Expr*y){size_t nx=conj_n(x),ny=conj_n(y);EV common={0},xo={0},yo={0};for(size_t i=0;i<nx;i++){Expr*f=conj_at(x,i);if(conj_has(y,f))ev_push(&common,f);else ev_push(&xo,f);}for(size_t i=0;i<ny;i++){Expr*f=conj_at(y,i);if(!conj_has(x,f))ev_push(&yo,f);}if(common.n&&xo.n&&yo.n){Expr*a=xo.n==1?xo.v[0]:ex_list(r,E_AND,xo.n,xo.v),*b=yo.n==1?yo.v[0]:ex_list(r,E_AND,yo.n,yo.v),*inner=ex2(r,op,a,b);ev_push(&common,inner);Expr*out=common.n==1?common.v[0]:ex_list(r,E_AND,common.n,common.v);ev_free(&common);ev_free(&xo);ev_free(&yo);return out;}ev_free(&common);ev_free(&xo);ev_free(&yo);return ex2(r,op,x,y);}
static Expr* prettify_rec(Rumba*r,Expr*e,uint64_t mask){switch(e->k){case E_NOT:e=ex_unary(r,E_NOT,prettify_rec(r,e->u.unary,mask));break;case E_SCALE:e=ex_scale(r,e->u.scale.c,prettify_rec(r,e->u.scale.e,mask));break;case E_AND:case E_OR:case E_XOR:case E_ADD:case E_MUL:{EV v={0};for(size_t i=0;i<e->u.list.n;i++){Expr*q=prettify_rec(r,e->u.list.v[i],mask);if(q->k==e->k)for(size_t j=0;j<q->u.list.n;j++)ev_push(&v,q->u.list.v[j]);else ev_push(&v,q);}e=v.n==1?v.v[0]:ex_list(r,e->k,v.n,v.v);ev_free(&v);break;}default:break;}if(e->k==E_ADD&&e->u.list.n==3){for(size_t i=0;i<3;i++){Expr*t=e->u.list.v[i];if(t->k!=E_SCALE||t->u.scale.e->k!=E_AND||t->u.scale.e->u.list.n!=2)continue;Expr*a=peel(t->u.scale.e->u.list.v[0]),*b=peel(t->u.scale.e->u.list.v[1]);Expr*r0=peel(e->u.list.v[(i+1)%3]),*r1=peel(e->u.list.v[(i+2)%3]);if(!((ex_eq(r0,a)&&ex_eq(r1,b))||(ex_eq(r0,b)&&ex_eq(r1,a))))continue;uint64_t c=t->u.scale.c&mask;if(c==mask)return assoc2(r,E_OR,a,b);if(c==(mask&(mask-1)))return assoc2(r,E_XOR,a,b);}
        for(size_t i=0;i<3;i++){uint64_t ci,ca,cb;Expr *ic,*a,*b,*x,*y;scaled_term(e->u.list.v[i],mask,&ci,&ic);if(ic->k!=E_AND||ic->u.list.n!=2)continue;a=peel(ic->u.list.v[0]);b=peel(ic->u.list.v[1]);scaled_term(e->u.list.v[(i+1)%3],mask,&ca,&x);scaled_term(e->u.list.v[(i+2)%3],mask,&cb,&y);if(ca!=cb||!((ex_eq(x,a)&&ex_eq(y,b))||(ex_eq(x,b)&&ex_eq(y,a))))continue;if(ci==((0-ca)&mask))return scale_pretty(r,ca,assoc2(r,E_OR,a,b),mask);if(ci==((0-(ca+ca))&mask))return scale_pretty(r,ca,assoc2(r,E_XOR,a,b),mask);}}
    if(e->k==E_ADD&&e->u.list.n>3&&e->u.list.n<=10){for(size_t i=0;i<e->u.list.n;i++){uint64_t ci;Expr*ic;scaled_term(e->u.list.v[i],mask,&ci,&ic);for(size_t j=0;j<e->u.list.n;j++)if(j!=i){uint64_t ca;Expr*x;scaled_term(e->u.list.v[j],mask,&ca,&x);for(size_t k=j+1;k<e->u.list.n;k++)if(k!=i){uint64_t cb;Expr*y;scaled_term(e->u.list.v[k],mask,&cb,&y);if(ca!=cb||!conj_union_eq(ic,x,y))continue;Kind op;if(ci==((0-ca)&mask))op=E_OR;else if(ci==((0-(ca+ca))&mask))op=E_XOR;else continue;Expr*fact=scale_pretty(r,ca,factor_join(r,op,x,y),mask);EV out={0};for(size_t q=0;q<e->u.list.n;q++)if(q!=i&&q!=j&&q!=k)ev_push(&out,e->u.list.v[q]);ev_push(&out,fact);Expr*z=out.n==1?out.v[0]:ex_list(r,E_ADD,out.n,out.v);ev_free(&out);return prettify_rec(r,z,mask);}}}}
    if(e->k==E_ADD&&e->u.list.n==4){for(size_t ci0=0;ci0<4;ci0++){Expr*ct=peel(e->u.list.v[ci0]);if(ct->k!=E_CONST)continue;uint64_t base=ct->u.c&mask;size_t ids[3],q=0;for(size_t j=0;j<4;j++)if(j!=ci0)ids[q++]=j;for(size_t z=0;z<3;z++){size_t i=ids[z];uint64_t ci,ca,cb;Expr *ic,*a,*b,*x,*y;scaled_term(e->u.list.v[i],mask,&ci,&ic);if(ic->k!=E_AND||ic->u.list.n!=2)continue;a=peel(ic->u.list.v[0]);b=peel(ic->u.list.v[1]);size_t j0=ids[(z+1)%3],j1=ids[(z+2)%3];scaled_term(e->u.list.v[j0],mask,&ca,&x);scaled_term(e->u.list.v[j1],mask,&cb,&y);if(ca!=base||cb!=base||!((ex_eq(x,a)&&ex_eq(y,b))||(ex_eq(x,b)&&ex_eq(y,a))))continue;uint64_t k=(0-base)&mask;if(ci==k)return scale_pretty(r,k,not_smaller(r,assoc2(r,E_OR,a,b)),mask);if(ci==((k+k)&mask))return scale_pretty(r,k,not_smaller(r,assoc2(r,E_XOR,a,b)),mask);}}}
    if(e->k==E_ADD&&e->u.list.n>=2&&e->u.list.n<=8){for(size_t i=0;i<e->u.list.n;i++){uint64_t ca;Expr*a;scaled_term(e->u.list.v[i],mask,&ca,&a);for(size_t j=0;j<e->u.list.n;j++)if(j!=i){uint64_t cj;Expr*ij;scaled_term(e->u.list.v[j],mask,&cj,&ij);if(cj!=((0-ca)&mask)||ij->k!=E_AND||ij->u.list.n<2)continue;for(size_t k=0;k<ij->u.list.n;k++)if(ex_eq(peel(ij->u.list.v[k]),a)){EV rest={0};for(size_t q=0;q<ij->u.list.n;q++)if(q!=k)ev_push(&rest,ij->u.list.v[q]);Expr*b=rest.n==1?rest.v[0]:ex_list(r,E_AND,rest.n,rest.v);Expr*fact=scale_pretty(r,ca,assoc2(r,E_AND,a,not_smaller(r,b)),mask);ev_free(&rest);EV out={0};for(size_t q=0;q<e->u.list.n;q++)if(q!=j)ev_push(&out,q==i?fact:e->u.list.v[q]);Expr*z=out.n==1?out.v[0]:ex_list(r,E_ADD,out.n,out.v);ev_free(&out);return prettify_rec(r,z,mask);}}}}
    if(e->k==E_ADD&&e->u.list.n==2){for(size_t i=0;i<2;i++){Expr*t=peel(e->u.list.v[i]);if(t->k!=E_CONST)continue;uint64_t c=t->u.c&mask,qc;Expr*q;scaled_term(e->u.list.v[1-i],mask,&qc,&q);if(qc==c)return scale_pretty(r,(0-c)&mask,not_smaller(r,q),mask);}}return e;}
static Expr* ccr_key_expr(Rumba*r,const HGKey*k){switch(k->k){case E_VAR:return ex_var(r,k->var);case E_CONST:return ex_const(r,k->c);case E_NOT:return ex_unary(r,E_NOT,ccr_key_expr(r,k->child));case E_SCALE:return ex_scale(r,k->c,ccr_key_expr(r,k->child));default:{EV v={0};for(size_t i=0;i<k->n;i++)ev_push(&v,ccr_key_expr(r,k->children[i]));Expr*q=v.n==1?v.v[0]:ex_list(r,k->k,v.n,v.v);ev_free(&v);return q;}}}
static Expr* ccr_restore(Rumba*r,Expr*e,HGKey**keys,size_t nk){if(e->k==E_VAR){if(e->u.var>=CARRIER_HBASE){size_t q=e->u.var-CARRIER_HBASE;if(q>=nk)return e;return ccr_key_expr(r,keys[q]);}return e;}if(e->k==E_CONST)return e;if(e->k==E_NOT)return ex_unary(r,E_NOT,ccr_restore(r,e->u.unary,keys,nk));if(e->k==E_SCALE)return ex_scale(r,e->u.scale.c,ccr_restore(r,e->u.scale.e,keys,nk));EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,ccr_restore(r,e->u.list.v[i],keys,nk));Expr*q=v.n==1?v.v[0]:ex_list(r,e->k,v.n,v.v);ev_free(&v);return q;}
typedef struct {uint64_t c;Expr**f;size_t nf;} CCRTerm;
static Expr* ccr_raw(Rumba*r,CCRTerm*t,size_t n){EV out={0};for(size_t i=0;i<n;i++){Expr*core=t[i].nf==0?ex_const(r,1):t[i].nf==1?t[i].f[0]:ex_list(r,E_MUL,t[i].nf,t[i].f);ev_push(&out,ex_scale(r,t[i].c,core));}Expr*q=out.n==0?ex_const(r,0):out.n==1?out.v[0]:ex_list(r,E_ADD,out.n,out.v);ev_free(&out);return q;}
static bool ccr_term_has(CCRTerm*t,Expr*f){for(size_t i=0;i<t->nf;i++)if(ex_eq(t->f[i],f))return true;return false;}
static size_t ccr_factor_cost(Rumba*r,Expr*f,HGKey**keys,size_t nk){return ex_size(ccr_restore(r,f,keys,nk));}
static size_t ccr_expr_projected_cost(Rumba*r,Expr*e,HGKey**keys,size_t nk){return ex_size(ccr_restore(r,e,keys,nk));}
static Expr* ccr_factor_terms(Rumba*r,CCRTerm*t,size_t n,HGKey**keys,size_t nk,unsigned depth){
    if(n<2||depth>=6)return ccr_raw(r,t,n);
    Expr**fac=NULL;size_t*cnt=NULL,fn=0,fc=0;
    for(size_t i=0;i<n;i++)for(size_t j=0;j<t[i].nf;j++){Expr*f=t[i].f[j];bool dup=false;for(size_t z=0;z<j;z++)if(ex_eq(t[i].f[z],f)){dup=true;break;}if(dup)continue;size_t q;for(q=0;q<fn;q++)if(ex_eq(fac[q],f))break;if(q==fn){if(fn==fc){fc=fc?fc*2:8;fac=realloc(fac,fc*sizeof(*fac));cnt=realloc(cnt,fc*sizeof(*cnt));if(!fac||!cnt){perror("realloc");exit(2);}}fac[fn]=f;cnt[fn]=0;fn++;}cnt[q]++;}
    size_t best=SIZE_MAX;uint64_t bg=0;for(size_t q=0;q<fn;q++)if(cnt[q]>=2){uint64_t g=(uint64_t)(cnt[q]-1)*(uint64_t)ccr_factor_cost(r,fac[q],keys,nk);if(best==SIZE_MAX||g>bg||(g==bg&&ex_cmp(fac[q],fac[best])<0)){best=q;bg=g;}}
    if(best==SIZE_MAX){free(fac);free(cnt);return ccr_raw(r,t,n);}Expr*f=fac[best];CCRTerm*grp=calloc(n,sizeof(*grp)),*rest=calloc(n,sizeof(*rest));size_t gn=0,rn=0;
    for(size_t i=0;i<n;i++){bool in=ccr_term_has(&t[i],f);CCRTerm*d=in?&grp[gn++]:&rest[rn++];d->c=t[i].c;d->nf=t[i].nf-(in?1:0);d->f=d->nf?malloc(d->nf*sizeof(Expr*)):NULL;if(in){bool removed=false;size_t w=0;for(size_t j=0;j<t[i].nf;j++){if(!removed&&ex_eq(t[i].f[j],f)){removed=true;continue;}d->f[w++]=t[i].f[j];}}else if(d->nf)memcpy(d->f,t[i].f,d->nf*sizeof(Expr*));}
    Expr*inside=ccr_factor_terms(r,grp,gn,keys,nk,depth+1);Expr*fact=ex2(r,E_MUL,f,inside);Expr*cand;if(rn){Expr*tail=ccr_factor_terms(r,rest,rn,keys,nk,depth+1);cand=ex2(r,E_ADD,tail,fact);}else cand=fact;Expr*raw=ccr_raw(r,t,n);
    size_t cc=ccr_expr_projected_cost(r,cand,keys,nk),rc=ccr_expr_projected_cost(r,raw,keys,nk);
    for(size_t i=0;i<gn;i++){free(grp[i].f);} for(size_t i=0;i<rn;i++){free(rest[i].f);} free(grp);free(rest);free(fac);free(cnt);return cc<rc?cand:raw;
}
static Expr* ccr_factor_carrier(Rumba*r,Expr*p,HGKey**keys,size_t nk){Expr**terms;size_t n;if(p->k==E_ADD){terms=p->u.list.v;n=p->u.list.n;}else{terms=&p;n=1;}CCRTerm*t=calloc(n,sizeof(*t));for(size_t i=0;i<n;i++){Expr*z=terms[i];uint64_t c=1;if(z->k==E_SCALE){c=z->u.scale.c;z=z->u.scale.e;}t[i].c=c;if(z->k==E_MUL){t[i].nf=z->u.list.n;t[i].f=malloc(t[i].nf*sizeof(Expr*));memcpy(t[i].f,z->u.list.v,t[i].nf*sizeof(Expr*));}else if(z->k==E_CONST){t[i].c*=z->u.c;t[i].nf=0;}else{t[i].nf=1;t[i].f=malloc(sizeof(Expr*));t[i].f[0]=z;}}Expr*q=ccr_factor_terms(r,t,n,keys,nk,0);for(size_t i=0;i<n;i++)free(t[i].f);free(t);return q;}
static Expr* ccr_word_factor_rec(Rumba*r,Expr*e,uint64_t mask,unsigned depth){
    if(depth>16)return e;
    if(e->k==E_NOT)e=ex_unary(r,E_NOT,ccr_word_factor_rec(r,e->u.unary,mask,depth+1));
    else if(e->k==E_SCALE)e=ex_scale(r,e->u.scale.c,ccr_word_factor_rec(r,e->u.scale.e,mask,depth+1));
    else if(e->k>=E_AND){EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,ccr_word_factor_rec(r,e->u.list.v[i],mask,depth+1));e=v.n==1?v.v[0]:ex_list(r,e->k,v.n,v.v);ev_free(&v);}
    e=prettify_rec(r,e,mask);
    if(e->k==E_ADD){for(unsigned pass=0;pass<4;pass++){Expr*c=ccr_factor_carrier(r,e,NULL,0);c=prettify_rec(r,c,mask);if(ex_size(c)>=ex_size(e))break;e=c;}}
    return e;
}

/* Canonical linear-MBA terminal renderer.
 * For F on q abstract bitwise atoms, choose c0=F(0) and partition the
 * Boolean cube by the other scalar values.  Each indicator chi_v has
 * chi_v(0)=0 and is reified as a pure bitwise formula by bounded Shannon
 * recursion.  F = c0 + sum_v (v-c0)*chi_v is therefore the same exact
 * linear-MBA carrier, with no SOURCE/target dependence. */
typedef struct { unsigned varset; uint64_t truth; Expr*e; size_t cost; bool used; } BoolMemoEnt;
typedef struct { BoolMemoEnt e[4096]; size_t n; Expr*vars[6]; uint64_t wordmask; Rumba*r; } BoolSynth;
static unsigned pc_u(unsigned x){unsigned n=0;while(x){x&=x-1;n++;}return n;}
static uint64_t bool_allmask(unsigned q){unsigned bits=1u<<q;return bits==64?UINT64_MAX:((UINT64_C(1)<<bits)-1);}
static uint64_t bool_cofactor(uint64_t f,unsigned q,unsigned pos,unsigned bit){unsigned nq=q-1,lim=1u<<nq;uint64_t out=0;for(unsigned j=0;j<lim;j++){unsigned lo=j&((1u<<pos)-1),hi=j>>pos,old=lo|(bit<<pos)|(hi<<(pos+1));if((f>>old)&1)out|=UINT64_C(1)<<j;}return out;}
static Expr* bs_not(BoolSynth*b,Expr*x){if(x->k==E_CONST)return ex_const(b->r,(~x->u.c)&b->wordmask);if(x->k==E_NOT)return x->u.unary;return ex_unary(b->r,E_NOT,x);}
static Expr* bs_and(BoolSynth*b,Expr*a,Expr*c){if(a->k==E_CONST){uint64_t x=a->u.c&b->wordmask;if(!x)return a;if(x==b->wordmask)return c;}if(c->k==E_CONST){uint64_t x=c->u.c&b->wordmask;if(!x)return c;if(x==b->wordmask)return a;}if(ex_eq(a,c))return a;return ex2(b->r,E_AND,a,c);}
static Expr* bs_or(BoolSynth*b,Expr*a,Expr*c){if(a->k==E_CONST){uint64_t x=a->u.c&b->wordmask;if(!x)return c;if(x==b->wordmask)return a;}if(c->k==E_CONST){uint64_t x=c->u.c&b->wordmask;if(!x)return a;if(x==b->wordmask)return c;}if(ex_eq(a,c))return a;return ex2(b->r,E_OR,a,c);}
static Expr* bs_xor(BoolSynth*b,Expr*a,Expr*c){if(a->k==E_CONST){uint64_t x=a->u.c&b->wordmask;if(!x)return c;if(x==b->wordmask)return bs_not(b,c);}if(c->k==E_CONST){uint64_t x=c->u.c&b->wordmask;if(!x)return a;if(x==b->wordmask)return bs_not(b,a);}if(ex_eq(a,c))return ex_const(b->r,0);return ex2(b->r,E_XOR,a,c);}
static bool bs_better(Expr*a,Expr*b){size_t ca=ex_size(a),cb=ex_size(b);return ca<cb||(ca==cb&&ex_cmp(a,b)<0);}
static Expr* bs_rec(BoolSynth*b,unsigned varset,uint64_t truth){unsigned q=pc_u(varset);truth&=bool_allmask(q);if(!truth)return ex_const(b->r,0);if(truth==bool_allmask(q))return ex_const(b->r,b->wordmask);for(size_t i=0;i<b->n;i++)if(b->e[i].used&&b->e[i].varset==varset&&b->e[i].truth==truth)return b->e[i].e;Expr*best=NULL;unsigned pos=0;for(unsigned oi=0;oi<6;oi++)if((varset>>oi)&1){uint64_t lo=bool_cofactor(truth,q,pos,0),hi=bool_cofactor(truth,q,pos,1);unsigned next=varset&~(1u<<oi);Expr*L=bs_rec(b,next,lo),*H=bs_rec(b,next,hi),*x=b->vars[oi],*cand=NULL;if(lo==hi)cand=L;else if(!lo&&hi==bool_allmask(q-1))cand=x;else if(lo==bool_allmask(q-1)&&!hi)cand=bs_not(b,x);else if(!lo)cand=bs_and(b,x,H);else if(!hi)cand=bs_and(b,bs_not(b,x),L);else if(lo==bool_allmask(q-1))cand=bs_or(b,bs_not(b,x),H);else if(hi==bool_allmask(q-1))cand=bs_or(b,x,L);else{Expr*c1=bs_or(b,bs_and(b,x,H),bs_and(b,bs_not(b,x),L));Expr*d=bs_xor(b,L,H);Expr*c2=bs_xor(b,L,bs_and(b,x,d));Expr*c3=bs_xor(b,H,bs_and(b,bs_not(b,x),d));cand=c1;if(bs_better(c2,cand))cand=c2;if(bs_better(c3,cand))cand=c3;}if(!best||bs_better(cand,best))best=cand;pos++;break;}if(b->n<4096){b->e[b->n]=(BoolMemoEnt){.varset=varset,.truth=truth,.e=best,.cost=ex_size(best),.used=true};b->n++;}return best;}
static void ccr_collect_ids(Expr*e,size_t*ids,size_t*n){if(e->k==E_VAR){for(size_t i=0;i<*n;i++)if(ids[i]==e->u.var)return;if(*n<6)ids[(*n)++]=e->u.var;else *n=7;return;}if(e->k==E_NOT)ccr_collect_ids(e->u.unary,ids,n);else if(e->k==E_SCALE)ccr_collect_ids(e->u.scale.e,ids,n);else if(e->k>=E_AND)for(size_t i=0;i<e->u.list.n&&*n<=6;i++)ccr_collect_ids(e->u.list.v[i],ids,n);}
static int szcmp_q(const void*a,const void*b){size_t x=*(const size_t*)a,y=*(const size_t*)b;return x<y?-1:x>y?1:0;}
static Expr* ccr_remap_ids(Rumba*r,Expr*e,size_t*ids,size_t n,Expr**dense){if(e->k==E_VAR){for(size_t i=0;i<n;i++)if(ids[i]==e->u.var)return dense[i];return e;}if(e->k==E_CONST)return e;if(e->k==E_NOT)return ex_unary(r,E_NOT,ccr_remap_ids(r,e->u.unary,ids,n,dense));if(e->k==E_SCALE)return ex_scale(r,e->u.scale.c,ccr_remap_ids(r,e->u.scale.e,ids,n,dense));EV v={0};for(size_t i=0;i<e->u.list.n;i++)ev_push(&v,ccr_remap_ids(r,e->u.list.v[i],ids,n,dense));Expr*q=v.n==1?v.v[0]:ex_list(r,e->k,v.n,v.v);ev_free(&v);return q;}
static bool ccr_linear_only(Expr*e){if(e->k==E_MUL)return false;if(e->k==E_NOT)return ccr_linear_only(e->u.unary);if(e->k==E_SCALE)return ccr_linear_only(e->u.scale.e);if(e->k>=E_AND)for(size_t i=0;i<e->u.list.n;i++)if(!ccr_linear_only(e->u.list.v[i]))return false;return true;}
static Expr* bs_anf(BoolSynth*b,unsigned q,uint64_t truth,size_t*ids){unsigned len=1u<<q;unsigned char a[64]={0};for(unsigned i=0;i<len;i++)a[i]=(truth>>i)&1;for(unsigned bit=0;bit<q;bit++)for(unsigned m=0;m<len;m++)if(m&(1u<<bit))a[m]^=a[m^(1u<<bit)];EV terms={0};for(unsigned m=0;m<len;m++)if(a[m]){if(m==0){ev_push(&terms,ex_const(b->r,b->wordmask));continue;}EV fs={0};for(unsigned j=0;j<q;j++)if(m&(1u<<j))ev_push(&fs,ex_var(b->r,ids[j]));Expr*t=fs.n==1?fs.v[0]:ex_list(b->r,E_AND,fs.n,fs.v);ev_free(&fs);ev_push(&terms,t);}Expr*out=terms.n==0?ex_const(b->r,0):terms.n==1?terms.v[0]:ex_list(b->r,E_XOR,terms.n,terms.v);ev_free(&terms);return out;}
static Expr* ccr_linear_render(Rumba*r,Expr*carrier,HGKey**keys,size_t nk,uint64_t mask){if(!carrier||!ccr_linear_only(carrier)||ex_size(carrier)<6)return NULL;size_t ids[6],q=0;ccr_collect_ids(carrier,ids,&q);if(q==0||q>4)return NULL;qsort(ids,q,sizeof(size_t),szcmp_q);Expr*dense[6];for(size_t i=0;i<q;i++)dense[i]=ex_var(r,i);Expr*red=ccr_remap_ids(r,carrier,ids,q,dense);size_t len=((size_t)1)<<q;uint64_t*sig=truth_table(red,q,mask);if(!sig)return NULL;uint64_t c0=sig[0]&mask,vals[16];size_t nv=0;for(size_t i=1;i<len;i++){uint64_t v=sig[i]&mask;if(v==c0)continue;bool seen=false;for(size_t j=0;j<nv;j++)if(vals[j]==v){seen=true;break;}if(!seen){if(nv==16){free(sig);return NULL;}vals[nv++]=v;}}if(nv==0){free(sig);return ex_const(r,c0);}BoolSynth bs={.wordmask=mask,.r=r};for(size_t i=0;i<q;i++)bs.vars[i]=ex_var(r,ids[i]);EV ta={0},tb={0};if(c0){ev_push(&ta,ex_const(r,c0));ev_push(&tb,ex_const(r,c0));}for(size_t j=0;j<nv;j++){uint64_t tm=0;for(size_t i=0;i<len;i++)if((sig[i]&mask)==vals[j])tm|=UINT64_C(1)<<i;Expr*pa=bs_anf(&bs,(unsigned)q,tm,ids);Expr*pb=bs_rec(&bs,(1u<<q)-1,tm);uint64_t delta=(vals[j]-c0)&mask;if(delta){ev_push(&ta,ex_scale(r,delta,pa));ev_push(&tb,ex_scale(r,delta,pb));}}free(sig);Expr*ca=ta.n==0?ex_const(r,0):ta.n==1?ta.v[0]:ex_list(r,E_ADD,ta.n,ta.v);Expr*cb=tb.n==0?ex_const(r,0):tb.n==1?tb.v[0]:ex_list(r,E_ADD,tb.n,tb.v);ev_free(&ta);ev_free(&tb);Expr*oa=prettify_rec(r,ccr_restore(r,ca,keys,nk),mask);Expr*ob=prettify_rec(r,ccr_restore(r,cb,keys,nk),mask);return ex_size(ob)<ex_size(oa)||(ex_size(ob)==ex_size(oa)&&ex_cmp(ob,oa)<0)?ob:oa;}
static Expr* ccr_terminal(Rumba*r,Expr*carrier,HGKey**keys,size_t nk,uint64_t mask){if(!carrier)return NULL;Expr*fact=ccr_factor_carrier(r,carrier,keys,nk);Expr*out=prettify_rec(r,ccr_restore(r,fact,keys,nk),mask);Expr*wf=ccr_word_factor_rec(r,out,mask,0);if(ex_size(wf)<ex_size(out))out=wf;Expr*lin=ccr_linear_render(r,carrier,keys,nk,mask);if(lin&&(ex_size(lin)<ex_size(out)||(ex_size(lin)==ex_size(out)&&ex_cmp(lin,out)<0)))out=lin;return out;}

static Expr* simplify(Rumba*r,Expr*e,unsigned n,bool*ok){uint64_t mask=mask_n(n);last_atom_carrier=NULL;last_atom_keys=NULL;last_atom_n=0;e=reduce_m(r,e,mask);size_t size=SIZE_MAX;for(int i=0;i<8;i++){Expr*next=simplify_inner(r,e,n,0,ok);if(!*ok)return e;size_t ns=ex_size(next);bool settled=ex_eq(next,e)||ns>=size;e=next;if(settled)break;size=ns;}Expr*base=prettify_rec(r,e,mask);if(ex_size(base)<12)return base;Expr*cand=ccr_terminal(r,last_atom_carrier,last_atom_keys,last_atom_n,mask);return cand&&ex_size(cand)<ex_size(base)?cand:base;}

static uint64_t rng64(uint64_t*x){*x^=*x<<13;*x^=*x>>7;*x^=*x<<17;return *x;}
static bool sem_equal(const Expr*a,const Expr*b,unsigned n,size_t samples){bool aa=false,bb=false;size_t ma=ex_maxvar(a,&aa),mb=ex_maxvar(b,&bb),m=(aa?ma:0)>(bb?mb:0)?(aa?ma:0):(bb?mb:0);size_t nv=(aa||bb)?m+1:1;uint64_t*vars=malloc(nv*sizeof(uint64_t)),mask=mask_n(n),seed=UINT64_C(0x123456789abcdef);for(size_t i=0;i<samples;i++){for(size_t j=0;j<nv;j++)vars[j]=rng64(&seed)&mask;if((ex_eval(a,vars,nv)&mask)!=(ex_eval(b,vars,nv)&mask)){free(vars);return false;}}free(vars);return true;}
static int run_case(const char*src,const char*want,unsigned n){Rumba r;arena_init(&r.arena);char err[256]={0};Expr*e=parse_expr(&r,src,err,sizeof err),*w=parse_expr(&r,want,err,sizeof err);if(!e||!w){fprintf(stderr,"parse failure: %s\n",err);arena_reset(&r.arena);return 1;}bool ok=true;Expr*q=simplify(&r,e,n,&ok);char*ss=ex_repr(q,n,false),*ww=ex_repr(w,n,false);bool sem=sem_equal(q,w,n,5000);printf("%-52s -> %-32s  %s%s\n",src,ss,ok?"ok":"ERR",sem?"":" SEMFAIL");free(ss);free(ww);arena_reset(&r.arena);return (!ok||!sem);}

static int hidden_restore_regression(void){
    Rumba r;arena_init(&r.arena);char err[256]={0};Expr*e=parse_expr(&r,"(v0 * (v0 | 2)) ^ 1",err,sizeof err);bool ok=true;Expr*q=e?simplify(&r,e,64,&ok):NULL;bool ia=false,oa=false;size_t im=e?ex_maxvar(e,&ia):0,om=q?ex_maxvar(q,&oa):SIZE_MAX;bool leak=!e||!q||!ok||(oa&&(!ia||om>im))||!sem_equal(e,q,64,5000);printf("hidden restore transitive/no-leak: %s\n",leak?"FAIL":"ok");arena_reset(&r.arena);return leak?1:0;
}

static int hc_regression_one(bool subset,bool gauge){
    Rumba r;arena_init(&r.arena);char err[256]={0};uint64_t mask=mask_n(4);int fail=0;
    Expr*root=parse_expr(&r,subset?"15 + v0 - v4 + (v2 & v4 & v3)":"(v2 & v3) + (v3 & v4)",err,sizeof err);root=reduce_m(&r,root,mask);
    Solver sol={.r=&r,.n=4,.mask=mask,.t=5,.degree=1};Expr*x=ex_var(&r,0);
    if(subset){
        hidden_push(&sol,2,x,NULL);hidden_push(&sol,3,ex_const(&r,1),NULL);
        Expr*d4=reduce_m(&r,ex2(&r,E_ADD,x,ex_const(&r,UINT64_MAX)),mask);if(gauge)d4=complement_expr(&r,d4,mask);hidden_push(&sol,4,d4,NULL);
        Expr*applied=hidden_cut_close(&sol,root);if(ex_eq(applied,root))fail=1;
        for(uint64_t xv=0;xv<16&&!fail;xv++){uint64_t vars[5]={xv,0,xv,1,gauge?((0-xv)&mask):((xv-1)&mask)};if((ex_eval(root,vars,5)&mask)!=(ex_eval(applied,vars,5)&mask))fail=1;}
    }else{
        Expr*d2=gauge?complement_expr(&r,x,mask):x;hidden_push(&sol,2,d2,NULL);hidden_push(&sol,3,reduce_m(&r,ex_scale(&r,2,x),mask),NULL);hidden_push(&sol,4,reduce_m(&r,ex2(&r,E_ADD,x,ex_const(&r,UINT64_MAX)),mask),NULL);
        Expr*applied=hidden_cut_close(&sol,root);if(ex_eq(applied,root))fail=1;
        for(uint64_t xv=0;xv<16&&!fail;xv++){uint64_t vars[5]={xv,0,gauge?((~xv)&mask):xv,(2*xv)&mask,(xv-1)&mask};if((ex_eval(root,vars,5)&mask)!=(ex_eval(applied,vars,5)&mask))fail=1;}
    }
    free(sol.h);arena_reset(&r.arena);return fail;
}
static int hidden_cut_regressions(void){int f=0;int a=hc_regression_one(false,false),b=hc_regression_one(false,true),c=hc_regression_one(true,false),d=hc_regression_one(true,true);printf("hidden-cut valuation direct/gauge: %s/%s\n",a?"FAIL":"ok",b?"FAIL":"ok");printf("hidden-cut subset direct/gauge:    %s/%s\n",c?"FAIL":"ok",d?"FAIL":"ok");f+=a+b+c+d;return f;}

static int self_test(void){
    int fail=0;
    fail+=run_case("(v0 ^ v1) + 2 * (v0 & v1)","v0 + v1",64);
    fail+=run_case("(v0 | v1) + (v0 & v1)","v0 + v1",64);
    fail+=run_case("v0 + v1 - 2 * (v0 & v1)","v0 ^ v1",64);
    fail+=run_case("-1 - v0","~v0",64);
    fail+=run_case("v0*v0 - v0*v0","0",64);
    fail+=run_case("(v0 & v1) + (v0 & v1)","2 * (v0 & v1)",64);
    /* Soundness regressions: dynamic-width Hidden Gauge + transitive hidden restoration. */
    fail+=run_case("v0 & 15","v0 & 15",64);
    fail+=run_case("v0 | 15","v0 | 15",64);
    fail+=run_case("v0 ^ 15","v0 ^ 15",64);
    fail+=hidden_restore_regression();

    /* Exact advanced regression cases from core/tests/test.rs on branch hidden. */
    fail+=run_case("-((v0 - v1 + 2 * (v1 & -v0)) & (-v1 + (v0 & v1))) + ((v0 + v1 - 2 * (v1 & (v0 - 1))) & (-v1 + (v0 & v1)))","0",64);
    fail+=run_case("-v3 - (v3 & 2*v4 & (v3+v4)) + (v3 & 2*v4) + (v3 & (v3+v4)) + (v3 & (-1 - 3*v4 - v3 + ((2*v4) & (v3+v4))))","0",64);
    fail+=run_case("-v0 + (v0 & (-1 - 3*v0 - v2 - (v2 & (-1 - 2*v0)))) + (v0 & (2*v2 + 3*v0 - (v2 & 2*v0)))","0",64);
    fail+=run_case("-(2*v2 & (v0+v2)) - (2*v2 & (v2*v2)) + (2*v2 & (v0+v2) & (v2*v2)) + (2*v2 & ((v0+v2) + ((-1-v0-v2) & (v2*v2))))","0",64);
    fail+=run_case("-v3 + (v3 & (-1 - v2*v3 - v3*v3 - v3*(v2 & (-1-v2-v3)))) + (v3 & (2*v2*v3 - v3*(v2 & (v2+v3)) + v3*v3))","0",64);
    fail+=run_case("-v5 - (v0 & v5 & (v4-v0-v3-(v4 & -v0))) + (v0 & v5) + (v5 & (v3-1-(v4 & (v0-1))+(v0 & (-v0-v3+(v4 & (v0-1)))))) + (v5 & (v4-v0-v3-(v4 & -v0)))","0",64);
    fail+=hidden_cut_regressions();
    return fail?1:0;
}
static char* trim_ws(char*s){while(*s&&isspace((unsigned char)*s))s++;char*e=s+strlen(s);while(e>s&&isspace((unsigned char)e[-1]))*--e=0;return s;}
static int u64_qcmp(const void*aa,const void*bb){uint64_t a=*(const uint64_t*)aa,b=*(const uint64_t*)bb;return a<b?-1:a>b?1:0;}
static uint64_t monotonic_ns(void){struct timespec ts;if(clock_gettime(CLOCK_MONOTONIC,&ts)!=0){perror("clock_gettime");exit(2);}return (uint64_t)ts.tv_sec*UINT64_C(1000000000)+(uint64_t)ts.tv_nsec;}
static int run_corpus_file(const char*path,unsigned n){
    FILE*f=fopen(path,"r");if(!f){perror(path);return 2;}char*line=NULL;size_t cap=0;ssize_t got;size_t count=0,okc=0,okzc=0,ngc=0,tcap=0;uint64_t*times=NULL,total_ns=0;
    while((got=getline(&line,&cap,f))>=0){(void)got;char*src=trim_ws(line);if(!*src)continue;char*comma=strchr(src,',');if(!comma){fprintf(stderr,"%s:%zu: expected two CSV columns\n",path,count+1);free(line);free(times);fclose(f);return 2;}*comma=0;char*mba_s=trim_ws(src),*gt_s=trim_ws(comma+1);count++;
        Rumba r;arena_init(&r.arena);char err[256]={0};Expr*mba=parse_expr(&r,mba_s,err,sizeof err);if(!mba){fprintf(stderr,"%s:%zu mba parse: %s\n",path,count,err);ngc++;arena_reset(&r.arena);continue;}Expr*gt=parse_expr(&r,gt_s,err,sizeof err);if(!gt){fprintf(stderr,"%s:%zu gt parse: %s\n",path,count,err);ngc++;arena_reset(&r.arena);continue;}
        bool sok=true;uint64_t t0=monotonic_ns();Expr*sm=simplify(&r,mba,n,&sok);uint64_t dt=monotonic_ns()-t0;if(count>tcap){tcap=tcap?tcap*2:1024;while(tcap<count)tcap*=2;times=realloc(times,tcap*sizeof(*times));}times[count-1]=dt;total_ns+=dt;if(!sok){ngc++;arena_reset(&r.arena);continue;}
        bool gok=true;Expr*sg=simplify(&r,gt,n,&gok);if(gok&&ex_eq(sm,sg)){okc++;arena_reset(&r.arena);continue;}
        bool dok=true;Expr*diff=reduce_m(&r,ex2(&r,E_ADD,mba,ex_neg(&r,gt)),mask_n(n));Expr*sd=simplify(&r,diff,n,&dok);if(dok&&sd->k==E_CONST&&((sd->u.c&mask_n(n))==0))okzc++;else ngc++;arena_reset(&r.arena);
    }
    fclose(f);free(line);if(!count){free(times);fprintf(stderr,"empty corpus\n");return 2;}qsort(times,count,sizeof(*times),u64_qcmp);uint64_t med=times[count/2],p95=times[(count*95)/100<count?(count*95)/100:count-1];printf("CORPUS %s count=%zu OK=%zu OKZ=%zu NG=%zu median=%.3f us p95=%.3f us total=%.3f ms\n",path,count,okc,okzc,ngc,(double)med/1e3,(double)p95/1e3,(double)total_ns/1e6);free(times);return ngc?1:0;
}

static int run_quality_corpus_file(const char*path,unsigned n){FILE*f=fopen(path,"r");if(!f){perror(path);return 2;}char*line=NULL;size_t cap=0;ssize_t got;size_t count=0,okc=0,okzc=0,ngc=0,w=0,t=0,l=0;uint64_t ast=0,raw=0;while((got=getline(&line,&cap,f))>=0){(void)got;char*src=trim_ws(line);if(!*src)continue;char*comma=strchr(src,',');if(!comma)continue;*comma=0;char*a=trim_ws(src),*b=trim_ws(comma+1);count++;Rumba r;arena_init(&r.arena);char err[256]={0};Expr*m=parse_expr(&r,a,err,sizeof err),*g=parse_expr(&r,b,err,sizeof err);if(!m||!g){ngc++;arena_reset(&r.arena);continue;}size_t rc=ex_size(g);raw+=rc;bool so=true;Expr*sm=simplify(&r,m,n,&so);if(!so){ngc++;arena_reset(&r.arena);continue;}size_t ac=ex_size(sm);ast+=ac;if(ac<rc)w++;else if(ac==rc)t++;else l++;bool go=true;Expr*sg=simplify(&r,g,n,&go);if(go&&ex_eq(sm,sg)){okc++;arena_reset(&r.arena);continue;}bool d=true;Expr*sd=simplify(&r,reduce_m(&r,ex2(&r,E_ADD,m,ex_neg(&r,g)),mask_n(n)),n,&d);if(d&&sd->k==E_CONST&&((sd->u.c&mask_n(n))==0))okzc++;else ngc++;arena_reset(&r.arena);}free(line);fclose(f);printf("QUALITY %s count=%zu OK=%zu OKZ=%zu NG=%zu W=%zu T=%zu L=%zu AST=%" PRIu64 " RAW=%" PRIu64 "\n",path,count,okc,okzc,ngc,w,t,l,ast,raw);return ngc?1:0;}

static int run_atom_carrier_corpus_file(const char*path,unsigned n){
    FILE*f=fopen(path,"r");if(!f){perror(path);return 2;}char*line=NULL;size_t cap=0;ssize_t got;size_t count=0,same=0,diff=0,same_n=0,diff_n=0;
    while((got=getline(&line,&cap,f))>=0){(void)got;char*src=trim_ws(line);if(!*src)continue;char*comma=strchr(src,',');if(!comma){free(line);fclose(f);return 2;}*comma=0;char*mba_s=trim_ws(src),*gt_s=trim_ws(comma+1);count++;Rumba r;arena_init(&r.arena);char err[256]={0};Expr*mba=parse_expr(&r,mba_s,err,sizeof err),*gt=parse_expr(&r,gt_s,err,sizeof err);if(!mba||!gt){diff++;arena_reset(&r.arena);continue;}
      bool ok=true;Expr*sm=simplify(&r,mba,n,&ok);Expr*cm=last_atom_carrier;size_t nm=last_atom_n;HGKey**km=last_atom_keys;
      ok=true;Expr*sg=simplify(&r,gt,n,&ok);Expr*cg=last_atom_carrier;size_t ng=last_atom_n;HGKey**kg=last_atom_keys;
      bool keys_same=nm==ng;for(size_t qi=0;keys_same&&qi<nm;qi++)keys_same=hg_cmp(km[qi],kg[qi])==0;
      if(keys_same)same_n++;else diff_n++;
      if(cm&&cg&&ex_eq(cm,cg)&&keys_same){same++;}else{diff++;if(diff<=20){char*a=cm?ex_repr(cm,n,false):strdup("NULL"),*b=cg?ex_repr(cg,n,false):strdup("NULL"),*aa=ex_repr(sm,n,false),*bb=ex_repr(sg,n,false);fprintf(stderr,"ATOM_DIFF %s:%zu n=%zu/%zu carrier=%s || %s out=%s || %s\n",path,count,nm,ng,a,b,aa,bb);free(a);free(b);free(aa);free(bb);}}
      arena_reset(&r.arena);
    }
    fclose(f);free(line);printf("ATOM_CARRIER %s count=%zu SAME=%zu DIFF=%zu SAME_N=%zu DIFF_N=%zu\n",path,count,same,diff,same_n,diff_n);return diff?1:0;
}

int main(int argc,char**argv){if(argc==2&&!strcmp(argv[1],"--self-test"))return self_test();unsigned n=32;bool hex=false,test=false;const char*src=NULL,*corpus=NULL,*atom_corpus=NULL,*quality_corpus=NULL;for(int i=1;i<argc;i++){if(!strcmp(argv[i],"--n")&&i+1<argc)n=(unsigned)strtoul(argv[++i],NULL,10);else if(!strcmp(argv[i],"--hex"))hex=true;else if(!strcmp(argv[i],"--test"))test=true;else if(!strcmp(argv[i],"--corpus")&&i+1<argc)corpus=argv[++i];else if(!strcmp(argv[i],"--atom-carrier-corpus")&&i+1<argc)atom_corpus=argv[++i];else if(!strcmp(argv[i],"--quality-corpus")&&i+1<argc)quality_corpus=argv[++i];else src=argv[i];}if(n==0||n>64){fprintf(stderr,"bit width must be 1..64\n");return 2;}if(atom_corpus)return run_atom_carrier_corpus_file(atom_corpus,n);if(quality_corpus)return run_quality_corpus_file(quality_corpus,n);if(corpus)return run_corpus_file(corpus,n);if(!src){fprintf(stderr,"usage: rumba-c [--n BITS] [--hex] [--test] 'expr' | --corpus file.csv\n");return 2;}Rumba r;arena_init(&r.arena);char err[256]={0};Expr*e=parse_expr(&r,src,err,sizeof err);if(!e){fprintf(stderr,"parse error: %s\n",err);arena_reset(&r.arena);return 2;}char*in=ex_repr(e,n,hex);printf("Simplify %s\n",in);free(in);bool ok=true;Expr*q=simplify(&r,e,n,&ok);if(!ok){fprintf(stderr,"solver rejected expression\n");arena_reset(&r.arena);return 1;}char*out=ex_repr(q,n,hex);printf("%s\n",out);free(out);if(test)printf("semantic random test: %s\n",sem_equal(e,q,n,10000)?"PASS":"FAIL");arena_reset(&r.arena);return 0;}
