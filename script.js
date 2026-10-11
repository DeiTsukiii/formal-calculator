const $=id=>document.getElementById(id);
const E=(t,c,...k)=>{const e=document.createElement(t);if(c)e.className=c;k.forEach(x=>e.append(x));return e};
/* ---------- modèle ---------- */
const root={nodes:[],parent:null};let cur={slot:root,i:0},ans=null;
const mkS=(n,a)=>{n.slots=a.map(s=>{const sl={nodes:[],parent:n};for(const ch of s)sl.nodes.push({t:'c',v:ch,parentSlot:sl});return sl});return n};
const mkM=(r,c)=>mkS({t:'mat',r,c},Array(r*c).fill(''));
const MK={
 frac:()=>mkS({t:'frac'},['','']),
 pow:()=>mkS({t:'pow'},['']),
 sqrt:()=>mkS({t:'sqrt'},['']),
 abs:()=>mkS({t:'abs'},['']),
 sin:()=>mkS({t:'fn',name:'sin',f:'sin'},['']),
 cos:()=>mkS({t:'fn',name:'cos',f:'cos'},['']),
 tan:()=>mkS({t:'fn',name:'tan',f:'tan'},['']),
 re:()=>mkS({t:'fn',name:'Re',f:'realpart'},['']),
 im:()=>mkS({t:'fn',name:'Im',f:'imagpart'},['']),
 conj:()=>mkS({t:'fn',name:'conj',f:'conjugate'},['']),
 arg:()=>mkS({t:'fn',name:'arg',f:'arg'},['']),
 prod:()=>mkS({t:'prod'},['','','','']),
 binom:()=>mkS({t:'binom'},['','']),
 dl:()=>mkS({t:'dl'},['','','','']),
 diffn:()=>mkS({t:'diffn'},['','','']),
 mat2:()=>mkM(2,2),
 mat3:()=>mkM(3,3),
 det:()=>mkS({t:'fn',name:'det',f:'determinant'},['']),
 inv:()=>mkS({t:'fn',name:'inv',f:'invert'},['']),
 transp:()=>mkS({t:'fn',name:'transp',f:'transpose'},['']),
 pgcd:()=>mkS({t:'fn',name:'pgcd',f:'gcd'},['']),
 ppcm:()=>mkS({t:'fn',name:'ppcm',f:'lcm'},['']),
 mod:()=>mkS({t:'fn',name:'mod',f:'mod'},['']),
 floor:()=>mkS({t:'fn',name:'floor',f:'floor'},['']),
 ceil:()=>mkS({t:'fn',name:'ceil',f:'ceil'},['']),
 log:()=>mkS({t:'fn',name:'log',f:'log10'},['']),
 ln:()=>mkS({t:'fn',name:'ln',f:'log'},['']),
 sum:()=>mkS({t:'sum'},['','','','']),
 defint:()=>mkS({t:'defint'},['','','','']),
 int:()=>mkS({t:'int'},['','']),
 diff:()=>mkS({t:'diff'},['','']),
 lim:()=>mkS({t:'lim'},['','','']),
};
const idx=n=>n.parentSlot.nodes.indexOf(n);
const isAl=n=>n&&n.t==='c'&&/^([0-9a-z.]|pi)$/i.test(n.v);
function ins(n){n.parentSlot=cur.slot;cur.slot.nodes.splice(cur.i,0,n);cur.i++;if(n.slots){const s=n.slots[n.focus||0];cur={slot:s,i:s.nodes.length}}}
function ch(v){ins({t:'c',v})}
function tpl(name){
  if(name==='frac'){const s=cur.slot;const j=opStart(s,cur.i);let mv=s.nodes.splice(j,cur.i-j);cur.i=j;if(mv.length>2&&wholeParen(mv))mv=mv.slice(1,-1);const f=MK.frac();ins(f);
    if(mv.length){f.slots[0].nodes=mv;mv.forEach(m=>m.parentSlot=f.slots[0]);cur={slot:f.slots[1],i:0}}return}
  if(name==='exp'){ch('e');ins(MK.pow());return}
  ins(MK[name]());
}
function right(){const s=cur.slot;
  if(cur.i<s.nodes.length){const n=s.nodes[cur.i];if(n.slots)cur={slot:n.slots[0],i:0};else cur.i++}
  else if(s.parent){const n=s.parent,k=n.slots.indexOf(s);if(k<n.slots.length-1)cur={slot:n.slots[k+1],i:0};else cur={slot:n.parentSlot,i:idx(n)+1}}}
function left(){const s=cur.slot;
  if(cur.i>0){const p=s.nodes[cur.i-1];if(p.slots){const l=p.slots[p.slots.length-1];cur={slot:l,i:l.nodes.length}}else cur.i--}
  else if(s.parent){const n=s.parent,k=n.slots.indexOf(s);if(k>0){const l=n.slots[k-1];cur={slot:l,i:l.nodes.length}}else cur={slot:n.parentSlot,i:idx(n)}}}
const empty=n=>!n.slots||n.slots.every(s=>!s.nodes.length);
function bs(){const s=cur.slot;
  if(cur.i>0){const p=s.nodes[cur.i-1];if(!p.slots||empty(p)){s.nodes.splice(cur.i-1,1);cur.i--}else left()}
  else if(s.parent){const n=s.parent;if(empty(n)){const ps=n.parentSlot,i=idx(n);ps.nodes.splice(i,1);cur={slot:ps,i}}else left()}}
/* ---------- rendu éditeur ---------- */
const SL=new WeakMap();
const D={'*':'×','-':'−','/':'÷',pi:'π',Infinity:'∞'};
const PHYS={
  c:{label:'c',value:'299792458'},
  G:{label:'G',value:'6.67430e-11'},
  h:{label:'h',value:'6.62607015e-34'},
  hbar:{label:'ℏ',value:'1.054571817e-34'},
  kB:{label:'kᵦ',value:'1.380649e-23'},
  NA:{label:'Nₐ',value:'6.02214076e23'},
  qe:{label:'e',value:'1.602176634e-19'},
  me:{label:'mₑ',value:'9.1093837015e-31'},
  mp:{label:'mₚ',value:'1.67262192369e-27'},
  R:{label:'R',value:'8.31446261815324'}
};
function rSlot(sl){const e=E('span','slot'+(sl.nodes.length||sl===root?'':' empty')+(cur.slot===sl&&sl!==root?' act':''));SL.set(e,sl);
  let last=null;
  sl.nodes.forEach((n,i)=>{let cr=false;if(cur.slot===sl&&cur.i===i){e.append(E('span','caret'));cr=true;last=null}
    const el=rNode(n);
    if(n.t==='pow'&&last&&!cr){const w=E('span','pb');last.replaceWith(w);w.append(last,el);last=w}
    else{e.append(el);last=el}});
  if(cur.slot===sl&&cur.i===sl.nodes.length)e.append(E('span','caret'));return e}
function rNode(n){const e=rNode0(n);if(anc.has(n))e.classList.add('in');return e}
function rNode0(n){const s=n.slots&&n.slots.map(rSlot);let e;
  switch(n.t){
  case 'c':e=E('span','ch'+(/^[+\-*\/=,]$/.test(n.v)?' op':(/^[a-df-hj-z]$/i.test(n.v)?' va':'')),D[n.v]||n.v);e._n=n;return e;
  case 'const':e=E('span','ch const',PHYS[n.name].label);e._n=n;return e;
  case 'ans':e=E('span','ch ans','Ans');e._n=n;return e;
  case 'frac':return E('span','frac',E('span','fn',s[0]),E('span','fd',s[1]));
  case 'pow':return E('sup','pw',s[0]);
  case 'sqrt':return E('span','rad','√',E('span','ov',s[0]));
  case 'abs':return E('span','fnc','|',s[0],'|');
  case 'fn':return E('span','fnc',E('span','nm',n.name),'(',s[0],')');
  case 'sum':return E('span','',E('span','sum',E('span','up',s[2]),E('span','sy','∑'),E('span','lo',s[0],'=',s[1])),s[3]);
  case 'defint':return E('span','fnc',E('span','intg',E('span','sy','∫'),E('span','lims',E('span','up',s[1]),E('span','lo',s[0]))),s[2],E('span','dd','\u00a0d'),s[3]);
  case 'int':return E('span','fnc',E('span','intg',E('span','sy','∫')),s[0],E('span','dd','\u00a0d'),s[1]);
  case 'diff':return E('span','fnc',E('span','frac',E('span','fn','d'),E('span','fd','d',s[0])),'(',s[1],')');
  case 'lim':return E('span','fnc',E('span','lim','lim',E('span','lo',s[0],'→',s[1])),s[2]);
  case 'prod':return E('span','',E('span','sum',E('span','up',s[2]),E('span','sy','∏'),E('span','lo',s[0],'=',s[1])),s[3]);
  case 'binom':return E('span','bn',E('span','bi',s[0]),E('span','bi',s[1]));
  case 'diffn':return E('span','fnc',E('span','frac',E('span','fn','d',E('span','pw2',s[1])),E('span','fd','d',s[0],E('span','pw2',plain(n.slots[1])||'n'))),'(',s[2],')');
  case 'dl':return E('span','fnc',E('span','lim','DL',E('span','lo',s[0],'→',s[1],' ; ordre ',s[2])),s[3]);
  case 'mat':{const g=E('span','mat');g.style.gridTemplateColumns=`repeat(${n.c},auto)`;s.forEach(x=>g.append(x));return g}
  }}
let anc=new Set();
const NM={sum:'Somme ∑',defint:'Intégrale ∫',int:'Primitive ∫',diff:'Dérivée d/dx',lim:'Limite',frac:'Fraction',pow:'Exposant',sqrt:'Racine',abs:'Valeur absolue',fn:'Fonction',prod:'Produit ∏',binom:'Binomial',diffn:'Dérivée n-ième',dl:'Développement limité',mat:'Matrice'};
const RL={sum:['variable','borne inférieure','borne supérieure','terme'],defint:['borne inférieure','borne supérieure','fonction','variable'],int:['fonction','variable'],diff:['variable','fonction'],lim:['variable','tend vers','fonction'],frac:['numérateur','dénominateur'],pow:['exposant'],sqrt:['sous la racine'],abs:['argument'],fn:['argument'],prod:['variable','borne inférieure','borne supérieure','terme'],binom:['n','k'],diffn:['variable','ordre','fonction'],dl:['variable','point','ordre','fonction']};
function draw(){const ed=$('ed');ed.innerHTML='';anc=new Set();const path=[];
  for(let s=cur.slot;s&&s.parent;s=s.parent.parentSlot){const n=s.parent;anc.add(n);path.unshift((n.t==='fn'?n.name:NM[n.t])+' › '+(n.t==='mat'?'ligne '+(Math.floor(n.slots.indexOf(s)/n.c)+1)+', col. '+(n.slots.indexOf(s)%n.c+1):RL[n.t][n.slots.indexOf(s)]))}
  $('ctx').textContent=path.length?path.join('  ▸  '):'Expression principale';
  ed.append(rSlot(root));const c=ed.querySelector('.caret');if(c)c.scrollIntoView({block:'nearest',inline:'nearest'})}
$('ed').addEventListener('click',e=>{
  const c=e.target.closest('.ch');
  if(c&&c._n){const r=c.getBoundingClientRect();cur={slot:c._n.parentSlot,i:idx(c._n)+(e.clientX>r.left+r.width/2?1:0)}}
  else{const s=e.target.closest('.slot');const sl=s?SL.get(s):root;cur={slot:sl,i:sl.nodes.length}}
  draw()});
/* ---------- sérialisation Nerdamer ---------- */
function ser(nodes){let o='',pv=null;
  for(const n of nodes){const it=one(n);if(pv&&pv.end&&it.start&&!(pv.dg&&it.dg))o+='*';o+=it.s;pv=it}return o}
function S(n,k){const r=ser(n.slots[k].nodes);if(!r)throw new Error('Complète toutes les cases vides.');return r}
function one(n){const T=(s)=>({s,start:true,end:true});
  switch(n.t){
  case 'c':{const v=n.v;if(/^[0-9.]$/.test(v))return{s:v,start:true,end:true,dg:true};
    if(/^[a-z]$/i.test(v)||v==='pi'||v==='Infinity')return T(v);
    if(v==='(')return{s:v,start:true,end:false};if(v===')'||v==='!')return{s:v,start:false,end:true};return{s:v,start:false,end:false}}
  case 'const':return T(`(${PHYS[n.name].value})`);
  case 'ans':return T(`(${ans})`);
  case 'frac':return T(`((${S(n,0)})/(${S(n,1)}))`);
  case 'pow':return{s:`^(${S(n,0)})`,start:false,end:true};
  case 'sqrt':return T(`sqrt(${S(n,0)})`);
  case 'abs':return T(`abs(${S(n,0)})`);
  case 'fn':return T(`${n.f}(${S(n,0)})`);
  case 'sum':return T(sumStr(S(n,3),S(n,0),S(n,1),S(n,2)));
  case 'defint':return T(defStr(S(n,2),S(n,3),S(n,0),S(n,1)));
  case 'int':return T(`integrate(${S(n,0)},${S(n,1)})`);
  case 'diff':return T(`diff(${S(n,1)},${S(n,0)})`);
  case 'lim':return T(limStr(S(n,2),S(n,0),S(n,1)));
  case 'prod':{const b=S(n,3),v=S(n,0),a=S(n,1),c=S(n,2);return T(b===v&&a==='1'?`factorial(${c})`:`product(${b},${v},${a},${c})`)}
  case 'binom':return T(`(factorial(${S(n,0)})/(factorial(${S(n,1)})*factorial((${S(n,0)})-(${S(n,1)}))))`);
  case 'diffn':return T(`diff(${S(n,2)},${S(n,0)},${S(n,1)})`);
  case 'dl':return T(dlStr(S(n,3),S(n,0),S(n,1),S(n,2)));
  case 'mat':{const rows=[];for(let i=0;i<n.r;i++){const r=[];for(let j=0;j<n.c;j++)r.push(S(n,i*n.c+j));rows.push(`[${r.join(',')}]`)}return T(`matrix(${rows.join(',')})`)}
  }}
/* ---------- sommes à bornes symboliques (formules de Faulhaber) ---------- */
const fr=(n,d)=>{if(d<0){n=-n;d=-d}const g=(a,b)=>b?g(b,a%b):Math.abs(a);const k=g(n,d)||1;return[n/k,d/k]};
const fadd=(a,b)=>fr(a[0]*b[1]+b[0]*a[1],a[1]*b[1]),fmul=(a,b)=>fr(a[0]*b[0],a[1]*b[1]);
const binom=(n,k)=>{let r=1;for(let i=1;i<=k;i++)r=r*(n-k+i)/i;return Math.round(r)};
let BN=null;
function bern(m){if(!BN){BN=[[1,1]];for(let i=1;i<=13;i++){let s=[0,1];for(let j=0;j<i;j++)s=fadd(s,fmul(fr(binom(i+1,j),1),BN[j]));BN.push(fmul(s,fr(-1,i+1)))}}return BN[m]}
function Tp(p,N){const parts=[];for(let j=0;j<=p;j++){let b=bern(j);if(j===1)b=[1,2];const c=fmul(fmul(fr(binom(p+1,j),1),b),fr(1,p+1));if(c[0]===0)continue;parts.push(`(${c[0]}/${c[1]})*(${N})^${p+1-j}`)}return parts.length?parts.join('+'):'0'}
function sumStr(body,v,a,b){
  const gen=`sum(${body},${v},${a},${b})`;
  if(/^-?\d+$/.test(a)&&/^-?\d+$/.test(b))return gen;
  try{const terms=[];let f=1,done=false;
    for(let p=0;p<=12;p++){if(p>0)f*=p;const ds=p===0?body:`diff(${body},${v},${p})`;
      if(p>0&&nerdamer(ds).toString()==='0'){done=true;break}
      const c=nerdamer(nerdamer(ds).toString(),{[v]:0}).toString();
      if(c!=='0')terms.push(`(${c})/${f}*((${Tp(p,b)})-(${Tp(p,`(${a})-1`)}))`)}
    if(done)return terms.length?`(${terms.join('+')})`:'0';
  }catch(e){}
  return guessSum(body,v,a,b)||gen}
/* ---------- limites & intégrales : calcul exact puis repli numérique ---------- */
const numf=(body,v)=>{try{return nerdamer(body).buildFunction([v])}catch(e){return null}};
const num=s=>parseFloat(nerdamer(s).evaluate().text('decimals'));
function nice(x){if(Math.abs(x)<1e-8)return'0';if(Math.abs(x-Math.E)<1e-7)return'e';if(Math.abs(x-Math.PI)<1e-7)return'pi';
  for(let q=1;q<=1000;q++){const p=Math.round(x*q);if(Math.abs(x-p/q)<1e-7)return q===1?`${p}`:`(${p}/${q})`}
  return x.toPrecision(10)}
function limStr(body,v,to){
  const gen=`limit(${body},${v},${to})`;
  try{const r=nerdamer(gen).toString();if(!/Infinity|limit\(|undefined|NaN/.test(r))return `(${r})`}catch(e){}
  try{const f=numf(body,v);if(!f)return gen;
    if(/Infinity/.test(to)){const s=/^-/.test(to)?-1:1;const [a,b,c]=[1e3,1e6,1e9].map(h=>f(s*h));
      if(Math.abs(c)>1e12)return (c<0?'-':'')+'Infinity';
      if(isFinite(c)&&Math.abs(c-b)<1e-5*(1+Math.abs(c)))return nice(c)}
    else{const x=num(to),h=1e-7,l=f(x-h),r=f(x+h);
      if(isFinite(l)&&isFinite(r)&&Math.abs(l-r)<1e-4*(1+Math.abs(r)))return nice((l+r)/2);
      if(Math.abs(l)>1e6&&Math.abs(r)>1e6&&Math.sign(l)===Math.sign(r))return (r<0?'-':'')+'Infinity'}
  }catch(e){}
  return gen}
function defStr(body,v,a,b){
  const gen=`defint(${body},${a},${b},${v})`;
  if(!/Infinity/.test(a+b)){
    try{const F=nerdamer(`integrate(${body},${v})`).toString();
      if(!/integrate\(/.test(F)){const Fb=nerdamer(F,{[v]:`(${b})`}).toString(),Fa=nerdamer(F,{[v]:`(${a})`}).toString();return `(${nerdamer(`(${Fb})-(${Fa})`).toString()})`}}catch(e){}
    try{const f=numf(body,v),A=num(a),B=num(b),N=2000,h=(B-A)/N;let s=f(A)+f(B);for(let i=1;i<N;i++)s+=f(A+i*h)*(i%2?4:2);const val=s*h/3;if(isFinite(val))return nice(val)}catch(e){}
  }
  return gen}
/* ---------- forme polaire (module · e^{i·argument}) ---------- */
function polarTex(e){
  const val=s=>parseFloat(nerdamer(s).evaluate().text('decimals'));
  let re=NaN,im=NaN;try{re=val(`realpart(${e})`);im=val(`imagpart(${e})`)}catch(_){}
  if(isNaN(re)||isNaN(im))return polarSym(e);
  const r=Math.hypot(re,im),th=Math.atan2(im,re);
  if(r<1e-12)return '0';
  let rs=null,ts=null;
  try{const s=nerdamer(`abs(${e})`).toString();if(Math.abs(val(s)-r)<1e-9*(1+r))rs=s}catch(_){}
  if(Math.abs(th)<1e-12)ts='0';else{const q=th/Math.PI;for(let d=1;d<=12&&!ts;d++){const p=Math.round(q*d);if(Math.abs(q-p/d)<1e-9)ts=(p<0?'-':'')+`(${Math.abs(p)}*pi/${d})`}}
  if(!ts)try{const s=nerdamer(`arg(${e})`).toString();if(/[a-z]/i.test(s)&&Math.abs(val(s)-th)<1e-9)ts=s}catch(_){}
  if(!rs)rs=nice(r);
  if(!ts){if(Math.abs(th)<1e-12)ts='0';else{const q=th/Math.PI;let f=null;for(let d=1;d<=12&&!f;d++){const p=Math.round(q*d);if(Math.abs(q-p/d)<1e-9)f=[p,d]}
    ts=f?(f[0]<0?'-':'')+`(${Math.abs(f[0])}*pi/${f[1]})`:th.toPrecision(10)}}
  if(ts==='0')return tx(rs);
  const neg=ts.startsWith('-'),t2=neg?ts.slice(1):ts,cx=/[+\-]/;
  const rp=rs==='1'?'':(cx.test(rs)?`\\left(${tx(rs)}\\right)`:tx(rs));
  const ex=cx.test(t2)?`\\left(${tx(t2)}\\right)`:tx(t2);
  return `${rp}e^{${neg?'-':''}i${ex}}`;
}
/* ---------- opérande pour fraction, annuler/rétablir, historique ---------- */
function opStart(s,i){let j=i;
  while(j>0){const p=s.nodes[j-1];
    if(p.slots||isAl(p)){j--;continue}
    if(p.t==='c'&&p.v===')'){let d=0,k=j-1;for(;k>=0;k--){const q=s.nodes[k];if(q.t!=='c')continue;if(q.v===')')d++;else if(q.v==='('){d--;if(d===0)break}}
      if(k<0)break;j=k;continue}
    break}
  return j}
function wholeParen(m){if(m[0].v!=='('||m[m.length-1].v!==')')return false;let d=0;for(let k=0;k<m.length;k++){const q=m[k];if(q.t!=='c')continue;if(q.v==='(')d++;else if(q.v===')'){d--;if(d===0&&k<m.length-1)return false}}return d===0}
const KEYS=['v','r','c','name','f','focus'];
function enc(nodes){return nodes.map(n=>{const o={t:n.t};KEYS.forEach(k=>{if(n[k]!==undefined)o[k]=n[k]});if(n.slots)o.s=n.slots.map(sl=>enc(sl.nodes));return o})}
function dec(arr,slot){return arr.map(o=>{const n={t:o.t,parentSlot:slot};KEYS.forEach(k=>{if(o[k]!==undefined)n[k]=o[k]});if(o.s)n.slots=o.s.map(a=>{const sl={nodes:[],parent:n};sl.nodes=dec(a,sl);return sl});return n})}
function pathOf(sl){const p=[];while(sl.parent){const n=sl.parent;p.unshift([n.parentSlot.nodes.indexOf(n),n.slots.indexOf(sl)]);sl=n.parentSlot}return p}
function slotAt(p){let sl=root;for(const [a,b] of p)sl=sl.nodes[a].slots[b];return sl}
const snapshot=()=>({e:enc(root.nodes),p:pathOf(cur.slot),i:cur.i});
function restore(sn){root.nodes=dec(sn.e,root);cur={slot:slotAt(sn.p),i:sn.i};draw()}
const UN=[],RE=[],NOPUSH=['left','right','undo','redo','arc','hyp','eq','expand','factor','simplify','solve','rect','polar','eig','partfrac','approx'];
function push(){UN.push(snapshot());if(UN.length>100)UN.shift();RE.length=0}
function undo(){if(!UN.length)return;RE.push(snapshot());restore(UN.pop())}
function redo(){if(!RE.length)return;UN.push(snapshot());restore(RE.pop())}
const HIST=[];let lastTex='';
async function drawHist(){const h=$('hist');h.innerHTML=HIST.map((x,i)=>`<div class="hi" data-i="${i}">\\[${x.rt}\\]</div>`).join('');try{await MathJax.typesetPromise([h])}catch(e){}}
function clearCalc(){push();root.nodes=[];cur={slot:root,i:0};draw()}
function pushHist(mode,rt){lastTex=rt+SUFFIX;clearCalc()}
$('tUndo').onclick=undo;$('tRedo').onclick=redo;
$('tCopy').onclick=()=>{try{navigator.clipboard.writeText(lastTex).then(()=>{$('tCopy').textContent='Copié ✓';setTimeout(()=>$('tCopy').textContent='Copier LaTeX',1200)})}catch(e){}};
document.addEventListener('click',ev=>{const h=ev.target.closest('.hi');if(h){push();restore(HIST[h.dataset.i].snap)}});
/* ---------- forme polaire symbolique (variables réelles) ---------- */
const FNRE=/determinant|invert|transpose|product|factorial|matrix|floor|ceil|gcd|lcm|mod|sec|csc|cot|asinh|acosh|atanh|asin|acos|atan|sinh|cosh|tanh|sin|cos|tan|conjugate|realpart|imagpart|arg|log10|log|exp|abs|sqrt|pi|Infinity|sum|diff|limit|integrate|defint/g;
function balArg(s,st){let d=0;for(let k=st;k<s.length;k++){if(s[k]==='(')d++;else if(s[k]===')'){d--;if(d===0)return s.slice(st+1,k)}}return null}
function polarSym(e){
  const vars=[...new Set(e.replace(FNRE,'').match(/[a-df-hj-z]/gi)||[])];
  const sub=k=>{const o={};vars.forEach((v,i)=>o[v]=(0.37+0.84*k+0.53*i).toFixed(3));return o};
  const val=(s,o)=>parseFloat(nerdamer(s,o).evaluate().text('decimals'));
  let th=null,m=e.match(/(?:cos|sin)\(/);
  if(m)th=balArg(e,m.index+m[0].length-1);
  else{m=e.match(/e\^\(/);if(m){const A=balArg(e,m.index+2);if(A)th=nerdamer(`(${A})/i`).toString()}}
  if(!th)throw new Error('Forme polaire : avec des variables, je reconnais cos(θ)+i·sin(θ) et e^(iθ) (éventuellement multipliés par une constante).');
  let r0=null;
  for(let k=0;k<3;k++){const o=sub(k),re=val(`realpart(${e})`,o),im=val(`imagpart(${e})`,o),t=val(th,o),r=Math.hypot(re,im);
    if(isNaN(re+im+t)||Math.abs(re-r*Math.cos(t))>1e-7||Math.abs(im-r*Math.sin(t))>1e-7)throw new Error('Forme polaire symbolique non trouvée.');
    if(r0===null)r0=r;else if(Math.abs(r-r0)>1e-7*(1+r0))throw new Error('Forme polaire symbolique non trouvée (le module dépend des variables).')}
  const rs=nice(r0),cx=/[+\-]/,neg=th.startsWith('-'),t2=neg?th.slice(1):th;
  const rp=rs==='1'?'':(cx.test(rs)?`\\left(${tx(rs)}\\right)`:tx(rs));
  const ex=cx.test(t2)?`\\left(${tx(t2)}\\right)`:tx(t2);
  return `${rp}e^{${neg?'-':''}i${ex}}`}
/* ---------- sommes classiques non polynomiales : candidats vérifiés numériquement ---------- */
function guessSum(body,v,a,b){
  try{
    if(!/^-?\d+$/.test(a))return null;
    const A=parseInt(a),syms=[...new Set(`${body}|${b}`.replace(FNRE,'').match(/[a-df-hj-z]/gi)||[])].filter(s=>s!==v);
    const bs=syms.filter(s=>new RegExp(`\\b${s}\\b`).test(b)),ps=syms.filter(s=>!bs.includes(s));
    const val=(s,o)=>parseFloat(nerdamer(s,o).evaluate().text('decimals'));
    const cands=['0'];
    ps.forEach(r=>{cands.push(`((${r})^((${b})+1)-(${r})^(${A}))/((${r})-1)`,`(1+${r})^(${b})`);ps.forEach(q=>{if(q!==r)cands.push(`((${r})+(${q}))^(${b})`)})});
    cands.push(`2^(${b})`,`(${b})*2^((${b})-1)`,`1-1/((${b})+1)`);
    const sets=[6,5].map((N,j)=>{const o={};bs.forEach(s=>o[s]=N);ps.forEach((s,i)=>o[s]=(0.7+0.45*i+0.3*j).toFixed(3));return o});
    const sums=sets.map(o=>{const NB=Math.round(val(b,o));if(!(NB>=A))throw 0;let S=0;for(let K=A;K<=NB;K++)S+=val(body,{...o,[v]:K});return S});
    for(const c of cands){let ok=true;for(let j=0;j<2&&ok;j++){const x=val(c,sets[j]);if(!isFinite(x)||Math.abs(x-sums[j])>1e-6*(1+Math.abs(sums[j])))ok=false}if(ok)return `(${c})`}
  }catch(e){}
  return null}
/* ---------- calcul saisi -> LaTeX (affiché à gauche du résultat) ---------- */
function texOf(nodes){
  let out='',lp=false;
  const s=sl=>texOf(sl.nodes);
  const CH={'*':'\\times ','/':'\\div ',pi:'\\pi ',Infinity:'\\infty '};
  for(const n of nodes){const q=n.slots?n.slots.map(s):[];let t='';
    switch(n.t){
      case 'c':t=CH[n.v]!==undefined?CH[n.v]:n.v;break;
      case 'const':t=PHYS[n.name].label;break;
      case 'ans':t='\\mathrm{Ans}';break;
      case 'frac':t=`\\frac{${q[0]}}{${q[1]}}`;break;
      case 'pow':t=`^{${q[0]}}`;if(!out||lp)t='{}'+t;break;
      case 'sqrt':t=`\\sqrt{${q[0]}}`;break;
      case 'abs':t=`\\left|${q[0]}\\right|`;break;
      case 'fn':t=`\\operatorname{${n.name}}\\left(${q[0]}\\right)`;break;
      case 'sum':t=`\\sum_{${q[0]}=${q[1]}}^{${q[2]}}${q[3]}`;break;
      case 'prod':t=`\\prod_{${q[0]}=${q[1]}}^{${q[2]}}${q[3]}`;break;
      case 'defint':t=`\\int_{${q[0]}}^{${q[1]}}${q[2]}\\,\\mathrm{d}${q[3]}`;break;
      case 'int':t=`\\int ${q[0]}\\,\\mathrm{d}${q[1]}`;break;
      case 'diff':t=`\\frac{\\mathrm{d}}{\\mathrm{d}${q[0]}}\\left(${q[1]}\\right)`;break;
      case 'diffn':t=`\\frac{\\mathrm{d}^{${q[1]}}}{\\mathrm{d}${q[0]}^{${q[1]}}}\\left(${q[2]}\\right)`;break;
      case 'lim':t=`\\lim_{${q[0]}\\to ${q[1]}}${q[2]}`;break;
      case 'binom':t=`\\binom{${q[0]}}{${q[1]}}`;break;
      case 'dl':t=`\\mathrm{DL}_{${q[2]}}\\left(${q[3]}\\right)_{${q[0]}\\to ${q[1]}}`;break;
      case 'mat':{const r=[];for(let i=0;i<n.r;i++)r.push(q.slice(i*n.c,(i+1)*n.c).join('&'));t=`\\begin{pmatrix}${r.join('\\\\')}\\end{pmatrix}`;break}
    }
    lp=n.t==='pow';out+=t}
  return out}
/* ---------- DL / Taylor-Young ---------- */
let SUFFIX='';
const plain=sl=>sl.nodes.map(n=>n.t==='c'?(D[n.v]||n.v):'·').join('');
function dlStr(body,v,a,n){
  const N=parseInt(n);if(!(N>=0&&N<=15))throw new Error('Ordre du DL : entier entre 0 et 15.');
  let f=1;const terms=[];
  for(let k=0;k<=N;k++){if(k>0)f*=k;
    const d=nerdamer(k===0?body:`diff(${body},${v},${k})`).toString();
    const c=nerdamer(d,{[v]:`(${a})`}).toString();
    if(c!=='0')terms.push(`(${c})/${f}*(${v}-(${a}))^${k}`)}
  SUFFIX=`+\\mathrm{o}\\left((${tx(v)}-${tx(a)})^{${N}}\\right)`;
  return terms.length?`(${terms.join('+')})`:'0'}
/* ---------- calcul ---------- */
const tx=s=>{try{return nerdamer.convertToLaTeX(s).replace(/Infinity/g,'\\infty')}catch(e){return s}};
function displayLogTex(tex,e){
  return /\blog\(/.test(e)?tex.replace(/\\mathrm\{log\}|\\log\b/g,'\\ln'):tex;
}
const scientificTex=s=>s
  .replace(/\\frac\{([^{}]+)\}\{1[eE]\+(\d+)\}/g,(_,coefficient,exponent)=>{
    return `${coefficient}\\times 10^{-${exponent}}`;
  })
  .replace(/([+-]?(?:\d+(?:\.\d*)?|\.\d+))[eE]([+-]?\d+)/g,(_,coefficient,exponent)=>{
  const sign=exponent.startsWith('-')?'-':'';
  const value=exponent.replace(/^[+-]/,'');
  return `${coefficient}\\times 10^{${sign}${value}}`;
  });
function pickVar(e){const m=e.replace(/determinant|invert|transpose|product|factorial|matrix|floor|ceil|gcd|lcm|mod|sec|csc|cot|asinh|acosh|atanh|asin|acos|atan|sinh|cosh|tanh|sin|cos|tan|conjugate|realpart|imagpart|arg|log|exp|abs|sqrt|pi|Infinity|sum|diff|limit|integrate|defint/g,'').match(/[a-df-hj-z]/i);return m?m[0]:'x'}
function equationToZero(e){
  let depth=0;
  for(let i=0;i<e.length;i++){
    if(e[i]==='('||e[i]==='[')depth++;
    else if(e[i]===')'||e[i]===']')depth--;
    else if(e[i]==='='&&depth===0)return `(${e.slice(0,i)})-(${e.slice(i+1)})`;
  }
  return e;
}
function hasEquation(e){
  let depth=0;
  for(const c of e){
    if(c==='('||c==='[')depth++;
    else if(c===')'||c===']')depth--;
    else if(c==='='&&depth===0)return true;
  }
  return false;
}
function equationVariable(e){
  const cleaned=e.replace(/determinant|invert|transpose|product|factorial|matrix|floor|ceil|gcd|lcm|mod|sec|csc|cot|asinh|acosh|atanh|asin|acos|atan|sinh|cosh|tanh|sin|cos|tan|conjugate|realpart|imagpart|arg|log10|log|exp|abs|sqrt|pi|Infinity|sum|diff|limit|integrate|defint/g,'');
  const m=cleaned.match(/[a-z]/i);
  return m?m[0]:null;
}
function periodicSolution(e){
  const fnRe=/^\s*(sin|cos|tan)\(\s*([a-z])\s*\)\s*=\s*(.+?)\s*$/i;
  let m=e.match(fnRe),fn,v,value;
  if(m){[,fn,v,value]=m}else{
    m=e.match(/^\s*(.+?)\s*=\s*(sin|cos|tan)\(\s*([a-z])\s*\)\s*$/i);
    if(!m)return null;
    [,value,fn,v]=m;
  }
  const key=value.replace(/\s+|\(|\)/g,'').toLowerCase();
  if(!['sin','cos','tan'].includes(fn.toLowerCase()))return null;
  if(!equationVariable(v))return null;
  const sets={
    sin:{
      '0':['0','\\pi'], '1':['\\frac{\\pi}{2}','2\\pi'], '-1':['-\\frac{\\pi}{2}','2\\pi'],
      'sqrt2/2':['\\frac{\\pi}{4},\\;\\frac{3\\pi}{4}','2\\pi'],
      '-sqrt2/2':['-\\frac{\\pi}{4},\\;-\\frac{3\\pi}{4}','2\\pi'],
      '1/2':['\\frac{\\pi}{6},\\;\\frac{5\\pi}{6}','2\\pi'],
      '-1/2':['-\\frac{\\pi}{6},\\;-\\frac{5\\pi}{6}','2\\pi'],
      'sqrt3/2':['\\frac{\\pi}{3},\\;\\frac{2\\pi}{3}','2\\pi'],
      '-sqrt3/2':['-\\frac{\\pi}{3},\\;-\\frac{2\\pi}{3}','2\\pi']
    },
    cos:{
      '0':['\\frac{\\pi}{2}','\\pi'], '1':['0','2\\pi'], '-1':['\\pi','2\\pi'],
      'sqrt2/2':['\\frac{\\pi}{4},\\;-\\frac{\\pi}{4}','2\\pi'],
      '-sqrt2/2':['\\frac{3\\pi}{4},\\;-\\frac{3\\pi}{4}','2\\pi'],
      '1/2':['\\frac{\\pi}{3},\\;-\\frac{\\pi}{3}','2\\pi'],
      '-1/2':['\\frac{2\\pi}{3},\\;-\\frac{2\\pi}{3}','2\\pi'],
      'sqrt3/2':['\\frac{\\pi}{6},\\;-\\frac{\\pi}{6}','2\\pi'],
      '-sqrt3/2':['\\frac{5\\pi}{6},\\;-\\frac{5\\pi}{6}','2\\pi']
    },
    tan:{
      '0':['0','\\pi'], '1':['\\frac{\\pi}{4}','\\pi'], '-1':['-\\frac{\\pi}{4}','\\pi'],
      'sqrt3':['\\frac{\\pi}{3}','\\pi'], '-sqrt3':['-\\frac{\\pi}{3}','\\pi'],
      '1/sqrt3':['\\frac{\\pi}{6}','\\pi'], '-1/sqrt3':['-\\frac{\\pi}{6}','\\pi']
    }
  };
  const group=sets[fn.toLowerCase()];
  const result=group&&group[key];
  return result?`${tx(v)}\\equiv ${result[0]}\\pmod{${result[1]}}`:null;
}
const LAB={eq:'Résultat',expand:'Développé',factor:'Factorisé',simplify:'Simplifié',solve:'Solutions',polar:'Forme polaire',rect:'Forme algébrique',eig:'Polynôme caractéristique et valeurs propres',partfrac:'Éléments simples',approx:'Valeur approchée',ediv:'Division euclidienne',study:'Étude de fonction'};
const FN={polar:'polarform',rect:'rectform'};
async function show(html,err){const o=$('out');o.className=err?'err':'';o.innerHTML=html;if(!err)try{await MathJax.typesetPromise([o])}catch(e){}}
function run(mode){
  try{
    SUFFIX='';if(!root.nodes.length)return;const e=ser(root.nodes);let qt=texOf(root.nodes);if(!e)throw new Error('Compose un calcul avant d’appuyer sur =.');
    if(mode==='solve'&&!hasEquation(e))qt+='=0';
    let o,rt;
    if(mode==='solve'){
      const equation=equationToZero(e),variable=equationVariable(e);
      if(!variable){
        o=nerdamer(equation).evaluate();
        const exact=o.toString();
        rt=exact==='0'?'\\text{identité vraie}':'\\text{aucune solution}';
      }else{
        const periodic=periodicSolution(e);
        if(periodic){o=nerdamer('0');rt=periodic}
        else{
          const v=pickVar(e);o=nerdamer(`solve(${equation},${v})`);
          const raw=o.toString().replace(/^\[|\]$/g,'');
          rt=raw?raw.split(',').map(s=>`${v}=${tx(s)}`).join('\\quad\\text{ou}\\quad '):'\\text{aucune solution}';
        }
      }
    }
    else if(mode==='study'){
      const v=pickVar(e),f=nerdamer(e),d=nerdamer(`diff(${e},${v})`),dd=nerdamer(`diff(${e},${v},2)`);
      o=f;
      const limNeg=nerdamer(`limit(${e},${v},-Infinity)`).toString();
      const limPos=nerdamer(`limit(${e},${v},Infinity)`).toString();
      rt=`\\begin{aligned}f(${v})&=${tx(f.toString())}\\\\f'(${v})&=${tx(d.toString())}\\\\f''(${v})&=${tx(dd.toString())}\\\\\\lim_{${v}\\to-\\infty}f&=${tx(limNeg)}\\\\\\lim_{${v}\\to+\\infty}f&=${tx(limPos)}\\end{aligned}`;
    }
    else if(mode==='polar'){o=nerdamer(e);rt=polarTex(e)}
    else if(mode==='eig'){const sz=nerdamer(`size(${e})`).toString().match(/\d+/);const n=sz?sz[0]:'2';o=nerdamer(`expand(determinant((${e})-t*imatrix(${n})))`);const rs=nerdamer(`solve(${o.toString()},t)`).toString().replace(/^\[|\]$/g,'');rt=`\\begin{aligned}\\chi(t)&=${o.toTeX()}\\\\ \\lambda&=${rs?rs.split(',').map(s=>tx(s)).join(',\\;'):'\\text{aucune}'}\\end{aligned}`}
    else if(mode==='ediv'){
      const tp=root.nodes.length===1&&root.nodes[0].t==='frac'?root.nodes[0]:null;
      if(!tp)throw new Error('Division euclidienne : saisis a⁄b avec la touche fraction (a divisé par b).');
      const A=ser(tp.slots[0].nodes),B=ser(tp.slots[1].nodes);
      if(!A||!B)throw new Error('Complète le dividende et le diviseur.');
      o=nerdamer('0');const isI=s=>/^-?\d+$/.test(s);let q,r;const ints=isI(A)&&isI(B);
      if(ints){const a=BigInt(A),b=BigInt(B);if(b===0n)throw new Error('Division par zéro.');let qq=a/b,rr=a%b;if(rr<0n){if(b>0n){qq-=1n;rr+=b}else{qq+=1n;rr-=b}}q=qq.toString();r=rr.toString()}
      else{const raw=nerdamer(`divide(${A},${B})`).toString().replace(/^\[|\]$/g,'');let d=0,k=-1;
        for(let i=0;i<raw.length;i++){const c=raw[i];if(c==='('||c==='[')d++;else if(c===')'||c===']')d--;else if(c===','&&d===0){k=i;break}}
        if(k<0)throw new Error('Division euclidienne impossible avec ces expressions.');q=raw.slice(0,k);r=raw.slice(k+1)}
      const P=s=>ints?(s.startsWith('-')?`(${s})`:s):/[+\-]/.test(s.replace(/^-/,''))?`\\left(${tx(s)}\\right)`:tx(s);
      rt=ints?`${A}=${P(B)}\\times ${P(q)}+${r}\\quad(0\\le r<${B.replace('-','')})`:`${tx(A)}=\\left(${tx(B)}\\right)\\left(${tx(q)}\\right)+${P(r)}`}
    else if(mode==='approx'){o=nerdamer(e);const ev=o.evaluate(),d=ev.text('decimals');rt=/^-?\d+(\.\d+)?(e[+-]?\d+)?$/i.test(d)?`\\approx ${d}`:`\\approx ${ev.toTeX().replace(/Infinity/g,'\\infty')}`}
    else if(mode==='partfrac'){o=nerdamer(`partfrac(${e},${pickVar(e)})`);rt=o.toTeX();ans=o.toString()}
    else{o=nerdamer(mode==='eq'?e:`${FN[mode]||mode}(${e})`);rt=tx(o.toString());try{rt=displayLogTex(o.toTeX().replace(/Infinity/g,'\\infty'),e)}catch(_){}
      ans=o.toString();
      }
    rt=scientificTex(rt);
    const un=/integrate\(|defint\(|limit\(|sum\(/.test(o.toString());
    show(`<span class="lab">${LAB[mode]}</span><div class="line"><div class="lq">\\[\\displaystyle ${qt}\\]</div><div class="lr">\\[\\displaystyle ${['solve','eig','approx','ediv'].includes(mode)?'':'= '}${rt}${SUFFIX}\\]</div></div>`+(un?'<span class="hint">Aucune forme simple trouvée (certaines intégrales, comme e^sin(x), n’ont pas de primitive élémentaire).</span>':''));
  pushHist(mode,rt);}catch(err){show(String(err.message||err).replace(/</g,'&lt;'),true)}
}
/* ---------- clavier ---------- */
const K=[
 ['xⁿ','pow','t'],['√','sqrt','t'],['∑','sum','t'],['∫ₐᵇ','defint','t'],
 ['∫','int','t'],['d/dx','diff','t'],['lim','lim','t'],['ln','ln','t'],['eˣ','exp','t'],
 ['sin','trig:sin','t'],['cos','trig:cos','t'],['tan','trig:tan','t'],['|x|','abs','t'],['π','c:pi','t'],
 ['arc','arc','a'],['hyp','hyp','a'],['i','c:i','t'],['∞','c:Infinity','o'],['Ans','ans','a'],
 ['x','c:x','o'],['y','c:y','o'],['z','c:z','o'],['n','c:n','o'],['k','c:k','o'],
 ['Développer','expand','a'],['Factoriser','factor','a'],['Simplifier','simplify','a'],['Résoudre','solve','a'],['Algébrique','rect','a'],
 ['Re','re','t'],['Im','im','t'],['z̄','conj','t'],['arg','arg','t'],['Polaire','polar','a'],
 ['7','c:7'],['8','c:8'],['9','c:9'],['(','c:('],[')','c:)'],
 ['4','c:4'],['5','c:5'],['6','c:6'],['×','c:*','o'],['÷','frac','o'],
 ['1','c:1'],['2','c:2'],['3','c:3'],['+','c:+','o'],['−','c:-','o'],
 ['0','c:0'],['.','c:.'],['◀','left','o'],['▶','right','o'],['⌫','bs','o'],
 ['AC','ac','a'],['','',''],['','',''],['','',''],['=','eq','eq']
].filter(k=>k[1]);
let ARC=false,HYP=false;
const trName=(b,d)=>d?(ARC?(HYP?'ar':'arc'):'')+b+(HYP?'h':''):(ARC?'a':'')+b+(HYP?'h':'');
function updKeys(){document.querySelectorAll('[data-tr]').forEach(b=>b.textContent=trName(b.dataset.tr,true));const x=$('b_arc'),y=$('b_hyp');if(x)x.classList.toggle('on',ARC);if(y)y.classList.toggle('on',HYP)}
function act(a){
  if(!NOPUSH.includes(a)&&!a.startsWith('mode:'))push();
  if(!root.nodes.length&&ans&&['c:+','c:*','frac','pow'].includes(a))ins({t:'ans'});
  if(a.startsWith('c:'))ch(a.slice(2));
  else if(a.startsWith('const:'))ins({t:'const',name:a.slice(6)});
  else if(a.startsWith('trig:')){ins(mkS({t:'fn',name:trName(a.slice(5),true),f:trName(a.slice(5),false)},['']))}
  else if(a==='arc'||a==='hyp'){if(a==='arc')ARC=!ARC;else HYP=!HYP;updKeys();return}
  else if(MK[a]||a==='exp')tpl(a);
  else if(a==='left')left();else if(a==='right')right();else if(a==='bs')bs();else if(a==='undo')undo();else if(a==='redo')redo();
  else if(a==='ans'){if(ans)ins({t:'ans'})}
  else if(a==='ac'){root.nodes=[];cur={slot:root,i:0};$('out').className='';$('out').innerHTML='<span class="hint">Prêt.</span>'}
  else if(a.startsWith('mode:')){MODE=a.slice(5);updMode();if(MODE==='ediv'&&!root.nodes.length){push();tpl('frac');draw()}return}
  else{if(!root.nodes.length)return;run(a==='eq'?MODE:a);return}
  draw()}
const mkKeys=(arr,host)=>arr.forEach(([l,a,c])=>{const b=E('button',c||'',l);if(a.startsWith('trig:'))b.dataset.tr=a.slice(5);if(a==='arc'||a==='hyp')b.id='b_'+a;b.onclick=()=>act(a);host.append(b)});
const K2=[
 ['∏','prod','t'],['n!','c:!','t'],['Cₙᵏ','binom','t'],['dⁿ/dxⁿ','diffn','t'],['DL','dl','t'],
 ['2×2','mat2','t'],['3×3','mat3','t'],['det','det','t'],['M⁻¹','inv','t'],['Mᵗ','transp','t'],
 ['Val. propres','eig','a'],['Él. simples','partfrac','a'],['pgcd','pgcd','t'],['ppcm','ppcm','t'],['mod','mod','t'],
 ['⌊x⌋','floor','t'],['⌈x⌉','ceil','t'],[',','c:,','o'],['a','c:a','o'],['b','c:b','o'],
 ['t','c:t','o'],['p','c:p','o'],['m','c:m','o'],['≈','approx','a'],['=','eq','eq2'],
 ['(','c:(','o'],[')','c:)','o'],['AC','ac','a'],['↶','undo','a'],['↷','redo','a']
];
const ICONS={analyse:'∫',fonctions:'ƒ',matrices:'▦',complexes:'ℂ',arith:'ℕ',vars:'α',physics:'⚛',mode:'≡'};
const MODEL={eq:'Calculer',expand:'Développer',factor:'Factoriser',simplify:'Simplifier',solve:'Résoudre',partfrac:'Él. simples',approx:'≈ Approché',polar:'Polaire',rect:'Algébrique',eig:'Val. propres',ediv:'Div. euclidienne',study:'Étude fonction'};
const MODEK=['eq','expand','factor','simplify','solve','partfrac','approx','ediv','study'].map(k=>[MODEL[k],'mode:'+k,'a']);
let MODE='eq';
function updMode(){const t=$('modeTag');if(t)t.textContent=MODE==='eq'?'':'Mode : '+MODEL[MODE];
  const b=document.querySelector('#pad [data-menu="mode"]');if(b){const lb=b.querySelector('.lb');if(lb)lb.textContent=MODEL[MODE];b.classList.toggle('on',MODE!=='eq')}
  const names=Object.values(MODEL);
  document.querySelectorAll('#menu .mg button').forEach(x=>{if(names.includes(x.textContent))x.classList.toggle('on',x.textContent===MODEL[MODE])})}
const STAY=['arc','hyp'];
const MENUS={
 analyse:{t:'Analyse',k:[['∑','sum','t'],['∏','prod','t'],['∫','int','t'],['∫ₐᵇ','defint','t'],['d/dx','diff','t'],['dⁿ/dxⁿ','diffn','t'],['lim','lim','t'],['DL','dl','t'],['∞','c:Infinity','o'],['=','c:=','o'],['Él. simples','mode:partfrac','a']]},
 fonctions:{t:'Fonctions',k:[['sin','trig:sin','t'],['cos','trig:cos','t'],['tan','trig:tan','t'],['arc','arc','a'],['hyp','hyp','a'],['ln','ln','t'],['log','log','t'],['eˣ','exp','t'],['|x|','abs','t'],['⌊x⌋','floor','t'],['⌈x⌉','ceil','t']]},
 matrices:{t:'Matrices',k:[['2×2','mat2','t'],['3×3','mat3','t'],['det','det','t'],['M⁻¹','inv','t'],['Mᵗ','transp','t'],['Val. propres','mode:eig','a']]},
 complexes:{t:'Complexes',k:[['i','c:i','t'],['z','c:z','o'],['Re','re','t'],['Im','im','t'],['z̄','conj','t'],['arg','arg','t'],['|z|','abs','t'],['Polaire','mode:polar','a'],['Algébrique','mode:rect','a']]},
 arith:{t:'Arithmétique',k:[['n!','c:!','t'],['Cₙᵏ','binom','t'],['pgcd','pgcd','t'],['ppcm','ppcm','t'],['Div. eucl.','mode:ediv','a']]},
 vars:{t:'Variables et constantes',k:[['y','c:y','o'],['z','c:z','o'],['a','c:a','o'],['b','c:b','o'],['c','c:c','o'],['k','c:k','o'],['n','c:n','o'],['p','c:p','o'],['t','c:t','o'],['e','c:e','o'],['i','c:i','o'],['π','c:pi','t'],['=','c:=','o'],['Ans','ans','a']]},
 physics:{t:'Constantes physiques',k:[['c','const:c','t'],['G','const:G','t'],['h','const:h','t'],['ℏ','const:hbar','t'],['kᵦ','const:kB','t'],['Nₐ','const:NA','t'],['e','const:qe','t'],['mₑ','const:me','t'],['mₚ','const:mp','t'],['R','const:R','t']]},
 mode:{t:'Mode de calcul (appliqué avec =)',k:MODEK}
};
const KM=[
 
 [[ICONS.analyse,'Analyse'],'menu:analyse','m'],[[ICONS.fonctions,'Fonctions'],'menu:fonctions','m'],[[ICONS.matrices,'Matrices'],'menu:matrices','m'],[[ICONS.complexes,'Complexes'],'menu:complexes','m'],[[ICONS.arith,'Arith.'],'menu:arith','m'],
 ['xⁿ','pow','t'],['√','sqrt','t'],['x','c:x','o'],[[ICONS.vars,'Variables'],'menu:vars','m'],[[ICONS.physics,'Physique'],'menu:physics','m'],
 ['7','c:7'],['8','c:8'],['9','c:9'],['(','c:('],[')','c:)'],
 ['4','c:4'],['5','c:5'],['6','c:6'],['×','c:*','o'],['÷','frac','o'],
 ['1','c:1'],['2','c:2'],['3','c:3'],['+','c:+','o'],['−','c:-','o'],
 ['0','c:0'],['.','c:.'],['◀','left','o'],['▶','right','o'],['⌫','bs','o'],
 ['AC','ac','a'],[[ICONS.mode,'Calculer'],'menu:mode','m'],[',','c:,','o'],['=','eq','eq']
];
function closeMenu(){$('menu').hidden=true}
function mkK(arr,host,inMenu){arr.forEach(([l,a,c])=>{const b=E('button',c||'',...(Array.isArray(l)?[E('span','ic',l[0]),E('span','lb',l[1])]:[l]));
  if(a.startsWith('trig:'))b.dataset.tr=a.slice(5);
  if(a==='arc'||a==='hyp')b.id='b_'+a;
  if(a.startsWith('menu:')){b.dataset.menu=a.slice(5);b.onclick=()=>{const h=$('menu');if(!h.hidden&&h.dataset.n===b.dataset.menu)closeMenu();else openMenu(b.dataset.menu)}}
  else b.onclick=()=>{act(a);if(inMenu&&!STAY.includes(a))closeMenu()};
  host.append(b)})}
function openMenu(name){const m=MENUS[name],h=$('menu');h.innerHTML='';h.dataset.n=name;
  const x=E('button','mx','✕');x.onclick=closeMenu;
  const g=E('div','pad mg');mkK(m.k,g,true);
  h.append(E('div','mh',E('span','',(ICONS[name]||'')+'  '+m.t),x),g);h.hidden=false;updKeys();updMode()}
mkK(KM,$('pad'),false);updMode();
document.addEventListener('click',ev=>{const t=ev.target;if(t.isConnected&&!t.closest('#menu')&&!t.closest('[data-menu]'))closeMenu()});

const FUNCS={ln:['ln','log'],log:['log','log10'],sec:['sec','sec'],csc:['csc','csc'],cot:['cot','cot'],conj:['conj','conjugate'],det:['det','determinant'],inv:['inv','invert'],pgcd:['pgcd','gcd'],ppcm:['ppcm','lcm'],mod:['mod','mod'],floor:['floor','floor'],ceil:['ceil','ceil']};
['sin','cos','tan'].forEach(b=>{FUNCS[b]=[b,b];FUNCS['a'+b]=FUNCS['arc'+b]=['arc'+b,'a'+b]});
const WORDS=[...Object.keys(FUNCS),'sqrt','abs','exp','pi','inf','sum','int','lim','diff','prod','binom'].sort((a,b)=>b.length-a.length);
const BR=['fn','sqrt','abs'];
function balanced(sl){let d=0;for(const n of sl.nodes){if(n.t==='c'){if(n.v==='(')d++;else if(n.v===')')d--}}return d<=0}
function typeLetter(c){
  const sl=cur.slot;
  if(c==='h'&&sl.parent&&sl.parent.t==='fn'&&!sl.nodes.length&&/^(arc)?(sin|cos|tan)$/.test(sl.parent.name)){const n=sl.parent;n.name=n.name.startsWith('arc')?'ar'+n.name.slice(3)+'h':n.name+'h';n.f+='h';return}
  ch(c);
  let j=cur.i,s='';const nd=cur.slot.nodes;
  while(j>0&&nd[j-1].t==='c'&&/^[a-z]$/i.test(nd[j-1].v)&&s.length<8){s=nd[j-1].v+s;j--}
  const m=WORDS.find(w=>s.toLowerCase().endsWith(w));if(!m)return;
  nd.splice(cur.i-m.length,m.length);cur.i-=m.length;
  if(FUNCS[m])ins(mkS({t:'fn',name:FUNCS[m][0],f:FUNCS[m][1]},['']));
  else if(m==='pi')ch('pi');else if(m==='inf')ch('Infinity');else tpl(m);
}
document.addEventListener('keydown',e=>{
  if((e.ctrlKey||e.metaKey)&&/^[zy]$/i.test(e.key)){e.preventDefault();(e.key.toLowerCase()==='z'&&!e.shiftKey)?undo():redo();return}
  if(e.ctrlKey||e.metaKey||e.altKey)return;
  if(e.key==='Tab'){e.preventDefault();if(e.shiftKey){cur.i=0;left()}else{cur.i=cur.slot.nodes.length;right()}draw();return}const k=e.key;let a=null;
  if(/^[a-z]$/i.test(k)){e.preventDefault();push();typeLetter(k);draw();return}
  if(k==='('&&cur.slot.parent&&BR.includes(cur.slot.parent.t)&&!cur.slot.nodes.length){e.preventDefault();return}
  if(k===')'&&cur.slot.parent&&BR.includes(cur.slot.parent.t)&&cur.i===cur.slot.nodes.length&&balanced(cur.slot)){e.preventDefault();right();draw();return}
  if(/^[0-9.+\-*(),!]$/.test(k))a='c:'+k;
  else if(k==='/')a='frac';else if(k==='^')a='pow';
  else if(k==='Enter')a='eq';
  else if(k==='=')a=MODE==='solve'?'c:=':'eq';
  else if(k==='Backspace')a='bs';
  else if(k==='ArrowLeft')a='left';else if(k==='ArrowRight')a='right';else if(k==='Escape')a='ac';
  if(a){e.preventDefault();act(a)}});
draw();