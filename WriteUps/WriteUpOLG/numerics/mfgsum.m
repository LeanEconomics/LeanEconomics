% The SUMMED Lasry-Lions pairing, which is all the path-equilibrium proof actually uses.
%   F_t(x,m) = -beta^t u( w(K(m)) y_t + (1+r(K(m))) a_t - a_{t+1} ),  K(m) = int a dm.
%   Candidate family: m(Khat) = optimal life-cycle behaviour at the prices of Khat.
%   Its own aggregate A(Khat) is what prices it inside F.  Same beta, same gamma, both sides.
function mfgsum
alpha=9/25; delta=2/25; J=60; rho=0.9; sigma=0.4; nz=7; beta=0.96;
[y,Pi,nu]=shocks(rho,sigma,nz);
na=800; ag=[0; exp(linspace(log(1e-3),log(4000),na-1))'];
frac=[0.50 0.65 0.80 0.90 0.95 0.98 1.02 1.05 1.10 1.20 1.50 2.00];
for gam=[1 2 3 5]
  rst=eqrate(beta,gam,alpha,delta,y,Pi,nu,J,ag);
  Kst=(alpha/(rst+delta))^(1/(1-alpha));
  n=numel(frac); C=cell(n,1);
  for i=1:n, C{i}=cand(Kst*frac(i),beta,gam,alpha,delta,y,Pi,nu,J,ag); end
  fprintf('\n=== gamma = %g :  r* = %+.4f,  K* = %.4f;  %d candidates, %d pairs ===\n',...
          gam,rst,Kst,n,n*(n-1)/2);
  fprintf('  Khat/K*  :'); fprintf(' %6.2f',frac); fprintf('\n');
  A=zeros(n,1); for i=1:n, A(i)=C{i}.A; end
  fprintf('  aggregate:'); fprintf(' %6.3f',A); fprintf('\n');
  minP=inf; minM=inf; nneg=0; npair=0; worstdate=0;
  for i=1:n, for k=i+1:n
    a=C{i}; b=C{k}; if a.A<b.A, t=a; a=b; b=t; end
    if abs(a.A-b.A)<1e-10, continue; end
    [Pd,~,neg]=summed(a,b,gam,ag,J,y,nz,beta);
    npair=npair+1;
    if Pd<0, nneg=nneg+1;
      fprintf('    FAILS: Khat/K* = %.2f (A=%.3f) vs %.2f (A=%.3f) : P = %+.6e\n',...
              frac(i),C{i}.A,frac(k),C{k}.A,Pd);
    end
    minP=min(minP,Pd); minM=min(minM,Pd/(a.A-b.A)^2); worstdate=max(worstdate,neg);
  end, end
  fprintf('  pairs with SUMMED pairing < 0 : %d of %d\n',nneg,npair);
  fprintf('  smallest summed pairing       : %+.6e\n',minP);
  fprintf('  smallest margin P/(A1-A2)^2   : %+.6f\n',minM);
  fprintf('  worst per-date count (P_t<0)  : %d of %d dates\n',worstdate,J);
  % restricted to the bracket the existence theorem proves: r in [2%, 8%]
  klo=(alpha/(0.08+delta))^(1/(1-alpha)); khi=(alpha/(0.02+delta))^(1/(1-alpha));
  sel=find(Kst*frac>=klo & Kst*frac<=khi);
  m2=inf; n2=0; p2=0;
  for ii=sel, for kk=sel
    if kk<=ii, continue; end
    a=C{ii}; b=C{kk}; if a.A<b.A, t=a; a=b; b=t; end
    if abs(a.A-b.A)<1e-10, continue; end
    Pd=summed(a,b,gam,ag,J,y,nz,beta); p2=p2+1; if Pd<0, n2=n2+1; end
    m2=min(m2,Pd/(a.A-b.A)^2);
  end, end
  fprintf('  inside the proved bracket K in [%.2f, %.2f]: %d of %d pairs fail, min margin %+.6f\n',...
          klo,khi,n2,p2,m2);
end
end
% candidate measure generated at the prices of Khat, plus the aggregate it actually carries
function E=cand(Kh,beta,gam,alpha,delta,y,Pi,nu,J,ag)
E.r=alpha*Kh^(alpha-1)-delta; E.w=(1-alpha)*Kh^alpha;
[S,E.mu,E.ap]=supply(1+E.r,beta,gam,y,Pi,nu,J,ag);
E.A=E.w*S;                              % the aggregate this measure carries
E.pr=alpha*E.A^(alpha-1)-delta;         % the price F pays it, from its OWN aggregate
E.pw=(1-alpha)*E.A^alpha;
end
function [Pd,Pu,neg]=summed(A,B,gam,ag,J,y,nz,beta)
Pd=0; Pu=0; neg=0;
for j=1:J
  d1=core(A,A,B,gam,ag,j,y,nz);
  d2=core(B,A,B,gam,ag,j,y,nz);
  P=-(d1-d2);
  Pd=Pd+beta^(j-1)*P; Pu=Pu+P; if P<0, neg=neg+1; end
end
end
function d=core(X,P1,P2,gam,ag,j,y,nz)
mu=X.mu(:,:,j); ap=X.ap(:,:,j); d=0;
for z=1:nz
  a=X.w*ag; s=X.w*ap(:,z);
  c1=P1.pw*y(z)+(1+P1.pr)*a-s;
  c2=P2.pw*y(z)+(1+P2.pr)*a-s;
  ok=(c1>1e-12)&(c2>1e-12);
  d=d+sum(mu(ok,z).*(uu(c1(ok),gam)-uu(c2(ok),gam)));
end
end
function r=eqrate(beta,gam,alpha,delta,y,Pi,nu,J,ag)
f=@(rr) supply(1+rr,beta,gam,y,Pi,nu,J,ag)-alpha/((1-alpha)*(rr+delta));
lo=-0.02; hi=0.60; flo=f(lo);
for it=1:40
  mid=0.5*(lo+hi); fm=f(mid);
  if flo*fm<=0, hi=mid; else, lo=mid; flo=fm; end
end
r=0.5*(lo+hi);
end
function [S,MU,AP]=supply(R,beta,gam,y,Pi,nu,J,ag)
nz=numel(y); na=numel(ag); c=egm(R,beta,gam,y,Pi,ag,J); m=y'+R*ag;
MU=zeros(na,nz,J); AP=zeros(na,nz,J); mu=zeros(na,nz); mu(1,:)=nu'; tot=0;
for j=0:J-1
  k=J-1-j; ap=max(m-c{k+1},0);
  MU(:,:,j+1)=mu; AP(:,:,j+1)=ap; tot=tot+sum(mu,2)'*ag;
  if j==J-1, break; end
  new=zeros(na,nz);
  for z=1:nz
    w=mu(:,z); x=min(max(ap(:,z),ag(1)),ag(end));
    bin=discretize(x,ag); bin(isnan(bin))=na-1; bin=max(min(bin,na-1),1);
    frac=(x-ag(bin))./(ag(bin+1)-ag(bin));
    new=new+accumarray([bin;bin+1],[w.*(1-frac);w.*frac],[na 1])*Pi(z,:);
  end
  mu=new;
end
S=tot/J;
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
function v=uu(c,g)
if abs(g-1)<1e-12, v=log(c); else, v=(c.^(1-g)-1)/(1-g); end
end
function [y,Pi,nu]=shocks(rho,sigma,nz)
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1); Pi=zeros(nz);
for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else, Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); nu=abs(V(:,k)); nu=nu/sum(nu);
y=exp(xg)'; y=y/(nu'*y);
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
