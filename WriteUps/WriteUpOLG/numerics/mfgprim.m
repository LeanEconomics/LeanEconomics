% Primitive conditions for the SUMMED Lasry-Lions condition in the OLG production economy.
%
% Reduction.  With U_i(K) the lifetime utility of PLAN i priced at aggregate K,
%     sum_t P_t  =  -[ U_1(K_1) - U_2(K_1) - U_1(K_2) + U_2(K_2) ],
% a mixed difference.  So summed monotonicity == U has DECREASING DIFFERENCES in (K, plan).
% Differentiating, dU_i/dK = r'(K) * Phi(K,i) with w'(K) = -K r'(K), where
%     Phi(K,i) = sum_t beta^t E_i[ u'(c_t) (a_t - K y_t) ]      (weighted net capital position).
% Since r' < 0 the condition is  Phi(K,plan1) >= Phi(K,plan2)  for the higher-saving plan 1.
%
% Two candidate primitive conditions, measured here:
%   (P) pointwise submodularity of the flow:  gam*(1+r(K))*(a_t - K y_t) <= c_t   everywhere;
%   (W) the weighted comparison Phi(K,1) >= Phi(K,2)  -- a scalar, strictly weaker than the
%       pointwise policy ordering a^1 >= a^2 (Light's Theorem 1), which is also measured.
function mfgprim
alpha=9/25; delta=2/25; J=60; rho=0.9; sigma=0.4; nz=7; beta=0.96;
[y,Pi,nu]=shocks(rho,sigma,nz);
na=800; ag=[0; exp(linspace(log(1e-3),log(4000),na-1))'];
for gam=[1 2 3 5]
  rst=eqrate(beta,gam,alpha,delta,y,Pi,nu,J,ag);
  Kst=(alpha/(rst+delta))^(1/(1-alpha));
  fprintf('\n=== gamma = %g :  r* = %+.4f,  K* = %.4f ===\n',gam,rst,Kst);
  for pr=[0.90 1.10; 0.98 1.02]'
    A=cand(Kst*pr(1),beta,gam,alpha,delta,y,Pi,nu,J,ag);   % lower Khat => higher r => saves more
    B=cand(Kst*pr(2),beta,gam,alpha,delta,y,Pi,nu,J,ag);
    fprintf('  plans at Khat/K* = %.2f and %.2f :  A_1 = %.4f > A_2 = %.4f\n',...
            pr(1),pr(2),A.A,B.A);
    % --- identity check: summed pairing vs the mixed difference of lifetime utility
    P=0; for j=1:J, P=P+beta^(j-1)*(-(core(A,A,B,gam,ag,j,y,nz)-core(B,A,B,gam,ag,j,y,nz))); end
    U11=lifetime(A,A,gam,ag,J,y,nz,beta); U12=lifetime(A,B,gam,ag,J,y,nz,beta);
    U21=lifetime(B,A,gam,ag,J,y,nz,beta); U22=lifetime(B,B,gam,ag,J,y,nz,beta);
    MD=U11-U21-U12+U22;
    fprintf('    summed pairing %+.8e ;  -(mixed difference) %+.8e ;  gap %.2e\n',P,-MD,abs(P+MD));
    % --- (P) pointwise submodularity
    for K=[B.A A.A]
      [frac,worst]=pointwise(A,gam,ag,J,y,nz,K,alpha,delta);
      [f2,w2]=pointwise(B,gam,ag,J,y,nz,K,alpha,delta);
      fprintf('    (P) at K=%6.3f : mass violating %.3f / %.3f ; worst gam(1+r)(a-Ky)-c = %+8.3f / %+8.3f\n',...
              K,frac,f2,worst,w2);
    end
    % --- (W) the weighted comparison
    fprintf('    (W) ');
    for K=[B.A 0.5*(A.A+B.A) A.A]
      p1=Phi(A,gam,ag,J,y,nz,K,alpha,delta); p2=Phi(B,gam,ag,J,y,nz,K,alpha,delta);
      fprintf('K=%6.3f: Phi1-Phi2 = %+9.5f   ',K,p1-p2);
    end
    fprintf('\n');
    % --- pointwise policy ordering in levels (Light's Theorem 1)
    [fb,wb]=ordering(A,B,ag,J,nz);
    fprintf('    (L) policy ordering a^1 >= a^2 in levels: violated on %.4f of plan-1 mass, worst %.4f\n',fb,wb);
  end
end
end
% ---------------------------------------------------------------- pieces
function v=lifetime(X,P,gam,ag,J,y,nz,beta)
v=0;
for j=1:J
  mu=X.mu(:,:,j); ap=X.ap(:,:,j);
  for z=1:nz
    c=P.pw*y(z)+(1+P.pr)*X.w*ag-X.w*ap(:,z); ok=c>1e-12;
    v=v+beta^(j-1)*sum(mu(ok,z).*uu(c(ok),gam));
  end
end
end
function [frac,worst]=pointwise(X,gam,ag,J,y,nz,K,alpha,delta)
r=alpha*K^(alpha-1)-delta; w=(1-alpha)*K^alpha; frac=0; worst=-inf;
for j=1:J
  mu=X.mu(:,:,j); ap=X.ap(:,:,j);
  for z=1:nz
    a=X.w*ag; c=w*y(z)+(1+r)*a-X.w*ap(:,z); ok=c>1e-12;
    g=gam*(1+r)*(a-K*y(z))-c;
    frac=frac+sum(mu(ok&g>0,z)); if any(ok), worst=max(worst,max(g(ok))); end
  end
end
frac=frac/J;
end
function v=Phi(X,gam,ag,J,y,nz,K,alpha,delta)
r=alpha*K^(alpha-1)-delta; w=(1-alpha)*K^alpha; v=0; beta=0.96;
for j=1:J
  mu=X.mu(:,:,j); ap=X.ap(:,:,j);
  for z=1:nz
    a=X.w*ag; c=w*y(z)+(1+r)*a-X.w*ap(:,z); ok=c>1e-12;
    v=v+beta^(j-1)*sum(mu(ok,z).*(c(ok).^(-gam)).*(a(ok)-K*y(z)));
  end
end
end
function [frac,worst]=ordering(A,B,ag,J,nz)
frac=0; worst=0;
for j=1:J
  mu=A.mu(:,:,j);
  for z=1:nz
    al=A.w*ag; s1=A.w*A.ap(:,z,j);
    s2=B.w*interp1(B.w*ag,B.ap(:,z,j),al,'linear','extrap');
    bad=s1<s2-1e-10; frac=frac+sum(mu(bad,z));
    if any(bad), worst=max(worst,max(s2(bad)-s1(bad))); end
  end
end
frac=frac/J;
end
function E=cand(Kh,beta,gam,alpha,delta,y,Pi,nu,J,ag)
E.r=alpha*Kh^(alpha-1)-delta; E.w=(1-alpha)*Kh^alpha;
[S,E.mu,E.ap]=supply(1+E.r,beta,gam,y,Pi,nu,J,ag);
E.A=E.w*S; E.pr=alpha*E.A^(alpha-1)-delta; E.pw=(1-alpha)*E.A^alpha;
end
function d=core(X,P1,P2,gam,ag,j,y,nz)
mu=X.mu(:,:,j); ap=X.ap(:,:,j); d=0;
for z=1:nz
  a=X.w*ag; s=X.w*ap(:,z);
  c1=P1.pw*y(z)+(1+P1.pr)*a-s; c2=P2.pw*y(z)+(1+P2.pr)*a-s;
  ok=(c1>1e-12)&(c2>1e-12);
  d=d+sum(mu(ok,z).*(uu(c1(ok),gam)-uu(c2(ok),gam)));
end
end
function r=eqrate(beta,gam,alpha,delta,y,Pi,nu,J,ag)
f=@(rr) supply(1+rr,beta,gam,y,Pi,nu,J,ag)-alpha/((1-alpha)*(rr+delta));
lo=-0.02; hi=0.60; flo=f(lo);
for it=1:40, mid=0.5*(lo+hi); fm=f(mid); if flo*fm<=0, hi=mid; else, lo=mid; flo=fm; end, end
r=0.5*(lo+hi);
end
function [S,MU,AP]=supply(R,beta,gam,y,Pi,nu,J,ag)
nz=numel(y); na=numel(ag); c=egm(R,beta,gam,y,Pi,ag,J); m=y'+R*ag;
MU=zeros(na,nz,J); AP=zeros(na,nz,J); mu=zeros(na,nz); mu(1,:)=nu'; tot=0;
for j=0:J-1
  k=J-1-j; ap=max(m-c{k+1},0); MU(:,:,j+1)=mu; AP(:,:,j+1)=ap; tot=tot+sum(mu,2)'*ag;
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
function v=uu(c,g), if abs(g-1)<1e-12, v=log(c); else, v=(c.^(1-g)-1)/(1-g); end, end
function [y,Pi,nu]=shocks(rho,sigma,nz)
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1); Pi=zeros(nz);
for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi0(hi); elseif j==nz, Pi(i,j)=1-Phi0(lo); else, Pi(i,j)=Phi0(hi)-Phi0(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); nu=abs(V(:,k)); nu=nu/sum(nu);
y=exp(xg)'; y=y/(nu'*y);
end
function v=Phi0(x), v=0.5*erfc(-x/sqrt(2)); end
