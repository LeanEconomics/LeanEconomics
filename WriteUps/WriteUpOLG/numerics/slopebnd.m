% How fast can capital supply fall?  The derivative-form increment route.
%   dS/dr >= -(1/J) sum_k G_k sum_z nu_z max_{a in reach} e_{k+1}(a,z),   e = (dc/dr - a)^+ = (-dg/dr)^+,
% with dc/dr bounded by the Lipschitz-in-r recursion obtained by differentiating the Euler fixed point
% c = Psi(m - c), Psi(x) = [beta R sum pi c_k(x,z')^-gam]^(-1/gam):
%   dc (1 + Psi_x) = dPsi_r + Psi_x a,   dPsi_r = -Psi/(gam R) + sum_z' w_z' dc_k(x,z'),  sum w = A(x) >= 1
% (A = (M_{-gam-1}/M_{-gam})^{-gam-1}, the power-mean amplification), Psi_x in [0, A s_k], s_k = max slope of c_k.
% Hence, with U/Lo upper/lower bounds on dc_k/dr,
%   v_up = -c/(gam R) + A max_z' U_k(x,z'),  U_{k+1} = max(v_up, (v_up + A s a)/(1 + A s)),
%   v_lo = -c/(gam R) + A min_z' Lo_k(x,z'),  Lo_{k+1} = min(v_lo, (v_lo + A s a)/(1 + A s)),  U_0 = Lo_0 = a,
% and at the corner (c = m) dc/dr = a exactly.  Everything below evaluates the recursion on the TRUE policies
% (what an enclosure-based proof would bound), and compares with the true dS/dr and with D'(r).
% If the bound beats D'(r) on a bracket, E = S - D is strictly increasing there: uniqueness, not just finiteness.
function slopebnd
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; alpha=9/25; delta=2/25;
[Pi,y,nu]=tauchen(rho,sigma,nz);
Dp=@(r) -alpha/((1-alpha)*(r+delta).^2);
na=600; ag=[0; exp(linspace(log(1e-3),log(300),na-1))'];
rs=0.02:0.005:0.08; dlt=1e-4;
fprintf('%s\n',datestr(now));
for gam=[1 2 3 5]
  fprintf('\ngamma = %g\n   r    | S      dS/dr(true) | D''(r)   | bound on dS/dr: exact-dc | recursion || mean e: true | recursion | worst U-a state (age,z,a) | max A\n',gam);
  for r=rs
    R=1+r;
    [S0,cS,e_true,edc]=supply(R,beta,gam,y,Pi,nu,ag,J,dlt);
    [Sm]=supply(R-dlt,beta,gam,y,Pi,nu,ag,J,0); [Sp]=supply(R+dlt,beta,gam,y,Pi,nu,ag,J,0);
    dS=(Sp-Sm)/(2*dlt);
    [bnd_rec,bnd_exact,me_true,me_rec,ws,Amax]=recursion(R,beta,gam,y,Pi,nu,ag,J,cS,edc);
    fprintf(' %.3f | %6.3f %+9.3f | %+8.2f | %+9.3f | %+9.3f || %7.4f | %7.4f | (%2d,%d,%6.2f) | %.4f\n',r,S0,dS,Dp(r),bnd_exact,bnd_rec,me_true,me_rec,ws,Amax);
  end
end
end

function [S,c,e_true,dc]=supply(R,beta,gam,y,Pi,nu,ag,J,dlt)
% S = olgCapital at rate R (true), c = stage consumption cells, dc = true dc/dr by central differences (if dlt>0)
nz=numel(y); na=numel(ag);
c=egm(R,beta,gam,y,Pi,ag,J); m=y'+R*ag; g=cell(J,1); for k=1:J, g{k}=max(m-c{k},0); end
A=ag*ones(1,nz);                                 % cohortAssets_0(a,z) = a
for k=1:J-1                                      % cohortAssets_{k}(a,z) = a + sum pi cohortAssets_{k-1}(g_k(a,z), z')
  An=zeros(na,nz);
  for z=1:nz
    acc=zeros(na,1);
    for zp=1:nz, acc=acc+Pi(z,zp)*interp1(ag,A(:,zp),min(g{k+1}(:,z),ag(end)),'linear'); end
    An(:,z)=ag+acc;
  end
  A=An;
end
S=(nu'*A(1,:)')/J;
e_true=[]; dc=[];
if dlt>0
  cm=egm(R-dlt,beta,gam,y,Pi,ag,J); cp=egm(R+dlt,beta,gam,y,Pi,ag,J);
  dc=cell(J,1); for k=1:J, dc{k}=(cp{k}-cm{k})/(2*dlt); end
end
end

function [bnd_rec,bnd_exact,me_true,me_rec,ws,Amax]=recursion(R,beta,gam,y,Pi,nu,ag,J,c,dc)
nz=numel(y); na=numel(ag); m=y'+R*ag; K=J-1;
Th=(beta*R)^(1/gam); kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
% reach by age from the true policies (age j has k = J-j periods to go; stage index k+1)
reach=zeros(J,1); a=0;
for j=1:J-1, k=J-j; a=max(max(y'+R*a-interp_row(ag,c{k+1},a)),0); reach(j+1)=a; end
U=ag*ones(1,nz); Lo=U; Amax=1; ws=[0 0 0]; wv=-Inf;
e_rec=zeros(J,1); e_tr=zeros(J,1);            % nu-weighted max failure at each age (index = age)
% age J (k=0): dc/dr = a exactly: e = 0
for k=0:K-1                                    % stage k -> k+1
  ck=c{k+1}; ck1=c{k+2}; g=max(m-ck1,0);
  s=max(max(diff(ck)./diff(ag)));              % max slope of c_k in a
  Un=zeros(na,nz); Ln=zeros(na,nz);
  for z=1:nz
    x=min(g(:,z),ag(end));
    cx=zeros(na,nz); Ux=zeros(na,nz); Lx=zeros(na,nz);
    for zp=1:nz
      cx(:,zp)=interp1(ag,ck(:,zp),x,'linear'); Ux(:,zp)=interp1(ag,U(:,zp),x,'linear'); Lx(:,zp)=interp1(ag,Lo(:,zp),x,'linear');
    end
    Psi=ck1(:,z);                              % = (beta R sum pi cx^-gam)^(-1/gam) where interior
    w=beta*R*(Pi(z,:).*cx.^(-gam-1)).*(Psi.^(gam+1));
    A=sum(w,2); Amax=max(Amax,max(A(g(:,z)>0)));
    vup=-Psi/(gam*R)+A.*max(Ux,[],2); vlo=-Psi/(gam*R)+A.*min(Lx,[],2);
    Un(:,z)=max(vup,(vup+A*s.*ag)./(1+A*s)); Ln(:,z)=min(vlo,(vlo+A*s.*ag)./(1+A*s));
    corner=g(:,z)<=0; Un(corner,z)=ag(corner); Ln(corner,z)=ag(corner);
  end
  U=Un; Lo=Ln;
  j=J-(k+1);                                   % age of a household at stage k+1
  ia=ag<=reach(j);
  for z=1:nz
    e_rec(j)=e_rec(j)+nu(z)*max([0; U(ia,z)-ag(ia)]);
    e_tr(j)=e_tr(j)+nu(z)*max([0; dc{k+2}(ia,z)-ag(ia)]);
    [mv,im]=max(U(ia,z)-ag(ia)); if mv>wv, wv=mv; aa=ag(ia); ws=[j z aa(im)]; end
  end
end
% envelope: e_1 = 0, e_{j+1} = L_j e_j + ebar_j, L_j = (1 - kappa_{J-j}) R;  bound = -mean_j e_j
L=zeros(J,1); for j=1:J, L(j)=(1-kap(J-j+1))*R; end
bnd_rec=-accum(L,e_rec,J); bnd_exact=-accum(L,e_tr,J);
me_true=mean(e_tr); me_rec=mean(e_rec);
end

function B=accum(L,ep,J)
e=0; tot=0;
for j=1:J, tot=tot+e; if j<J, e=L(j)*e+ep(j); end, end
B=tot/J;
end

function v=interp_row(ag,C,a)
nz=size(C,2); v=zeros(1,nz); for z=1:nz, v(z)=interp1(ag,C(:,z),a,'linear','extrap'); end
end

function c=egm(R,beta,gamma,y,Pi,ag,J)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); c{1}=m;
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z);
  end
  c{k+1}=min(cn,m);
end
end

function [Pi,y,nu]=tauchen(rho,sigma,nz)
sd=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd; hi=(xg(j)+h/2-rho*xg(i))/sd;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,Dg]=eig(Pi'); [~,k]=max(abs(diag(Dg))); nu=abs(V(:,k)); nu=nu/sum(nu);
y=exp(xg)'; y=y/(nu'*y);
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
