% The backward induction for Theorem 1 in the life cycle.
% Theorem 1 at stage k+1  <=>  c2_{k+1} - c1_{k+1} <= dr*a  (budget identity).
% Induction step at an interior state (a1'>0), given the claim at stage k:
%   need   R2 E[(c1_k(a1') + dr a1')^-g]  >=  R1 E[c1_k(a1')^-g] * (1 + dr a/c1)^-g     (*)
% Pointwise-in-z' sufficient version (the slack elasticity condition):
%   a1'/c1_k(a1',z') - a/c1_{k+1}(a,z) <= 1/(g R1)                                      (SEC)
function lc_induct(gamma,J)
beta=0.96; rho=0.9; sigma=0.4; nz=7;
r1=0.040; r2=0.041; R1=1+r1; R2=1+r2; dr=r2-r1;
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); p=abs(V(:,k)); p=p/sum(p); y=exp(xg)'; y=y/(p'*y);
na=4000; ag=[0; exp(linspace(log(1e-4),log(600),na-1))'];
[c1,g1]=egm_life(R1,beta,gamma,y,Pi,ag,J);
[c2,g2]=egm_life(R2,beta,gamma,y,Pi,ag,J);
amax=zeros(J,1);
for j=0:J-2, k=J-1-j; amax(j+2)=max(interp1(ag,g2{k+1},amax(j+1),'linear','extrap')); end
fprintf('\n===== gamma=%g J=%d : induction margins (>=0 means the step closes)\n',gamma,J);
fprintf('  k | region | min margin (*) /dr   at (a,z) | min SEC/dr | interior share | Thm1 max viol\n');
worst=inf; wk=0; wa=0; wz=0;
for k=1:J-1
  j=J-1-k; A=amax(j+1); sel=find(ag<=A+1e-12); if isempty(sel), sel=1; end
  C1=c1{k+1}; G1=g1{k+1}; Cp1=c1{k};
  mm=inf; ma=0; mz=0; msec=inf; nint=0; ntot=0; t1=0;
  for z=1:nz
    b=G1(sel,z); cb=interp_cols(ag,Cp1,b);            % c1_k(a1', z')
    int=b>1e-10; nint=nint+sum(int); ntot=ntot+numel(b);
    pz=Pi(z,:);
    L=log(R2)+log(((cb+dr*b).^(-gamma))*pz');
    Rh=log(R1)+log((cb.^(-gamma))*pz')-gamma*log(1+dr*ag(sel)./C1(sel,z));
    marg=(L-Rh)/dr; marg(~int)=inf;                    % corners are automatic
    [v,ix]=min(marg); if v<mm, mm=v; ma=ag(sel(ix)); mz=z; end
    sec=(1/(gamma*R1)-(b./cb-ag(sel)./C1(sel,z)));     % min over z' of the SEC slack
    sec=min(sec,[],2); sec(~int)=inf; msec=min(msec,min(sec));
    t1=max(t1,max(g1{k+1}(sel,z)-g2{k+1}(sel,z)));
  end
  if mm<worst, worst=mm; wk=k; wa=ma; wz=mz; end
  if ismember(k,[1 2 3 5 10 20 30 40 50 J-1])
    fprintf('%4d | %6.1f | %+9.3f at (%6.2f,%d) | %+9.3f | %5.1f%% | %.2e\n',...
      k,A,mm,ma,mz,msec,100*nint/ntot,t1);
  end
end
fprintf('  worst margin over all stages: %+.4f at stage %d, a=%.3f, z=%d\n',worst,wk,wa,wz);
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
function [c,g]=egm_life(R,beta,gamma,y,Pi,ag,J)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); g=cell(J,1); c{1}=m; g{1}=zeros(na,nz);
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z);
  end
  cn=min(cn,m); c{k+1}=cn; g{k+1}=m-cn;
end
end
function out=interp_cols(ag,c,b)
nz=size(c,2); out=zeros(numel(b),nz);
for z=1:nz, out(:,z)=interp1(ag,c(:,z),b,'linear','extrap'); end
end
