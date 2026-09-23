% Life-cycle (J periods, flat earnings, Aiyagari's Tauchen chain) at two interest rates.
% Stage k = periods still to come; age j = J-1-k. Checks, stage by stage, on the wealth
% region reachable from zero wealth at birth:
%   (1) Theorem 1: saving rises with the rate;
%   (2) the elasticity condition EC at the pivots;
%   (3) the slack condition SEC at the pivots;
%   (4) the backward recursion for the affine rate-response bound, from (alpha,B)=(1,0).
function lc_check(gamma,J)
beta=0.96; rho=0.9; sigma=0.4; nz=7;
r1=0.040; r2=0.041; R1=1+r1; R2=1+r2; dr=r2-r1;
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); p=abs(V(:,k)); p=p/sum(p); y=exp(xg)'; y=y/(p'*y);
na=2000; ag=[0; exp(linspace(log(1e-3),log(600),na-1))'];
fprintf('\n======== gamma=%g  J=%d  r1=%.3f r2=%.3f  y=%s\n',gamma,J,r1,r2,mat2str(y',3));
[c1,g1]=egm_life(R1,beta,gamma,y,Pi,ag,J); [c2,g2]=egm_life(R2,beta,gamma,y,Pi,ag,J);
% reachable wealth by age: amax(j+1) = max wealth at age j, starting from zero at birth
amax=zeros(J,1);
for j=0:J-2
  k=J-1-j;                               % stage used at age j
  amax(j+2)=max(interp1(ag,g2{k+1},amax(j+1),'linear','extrap'));
end
fprintf('reachable wealth by age (j=0,10,...): %s\n',mat2str(amax(1:10:end)',3));
% stage-by-stage checks
alpha=1; Bz=zeros(1,nz); rows=[]; failEC=[]; failSEC=[]; failT1=[];
for k=1:J-1
  j=J-1-k; A=amax(j+1); sel=ag<=A+1e-12; if ~any(sel), sel=1; end
  C1=c1{k+1}; C2=c2{k+1}; G1=g1{k+1}; G2=g2{k+1}; Cp1=c1{k}; Cp2=c2{k};
  t1=sum(sum(G1(sel,:)>G2(sel,:)+1e-9)); if t1>0, failT1(end+1)=k; end
  ecm=-inf; secm=inf; needmax=-inf(1,nz); secbmin=inf;
  for z=1:nz
    b=G1(:,z); c1b=interp_cols(ag,Cp1,b); c2b=interp_cols(ag,Cp2,b);
    lr=max(gamma*log(c2b./c1b),[],2);                  % log LHS
    ecm=max(ecm,max((lr(sel)-log(R2/R1))/dr));         % EC margin (>0 = violated)
    rhs=log(R2/R1)+gamma*log(1+dr*ag./C1(:,z));
    secm=min(secm,min((rhs(sel)-lr(sel))/dr));         % SEC margin (>0 = holds)
    % transfer step with the previous stage's affine bound
    a1=b; a2=G2(:,z); c1a1=c1b; c1a2=interp_cols(ag,Cp1,a2);
    X=max(c1a2-c1a1+dr*(alpha*a2+Bz),0); pz=Pi(z,:);
    Eu=(c1a1.^(-gamma))*pz'; EuX=((c1a1+X).^(-gamma))*pz';
    cb=(R1/R2)^(1/gamma)*C1(:,z).*(Eu./EuX).^(1/gamma);
    nd=(cb-C1(:,z))/dr; corner=a1<=1e-9; nd(corner)=ag(corner);   % corner: gap = a exactly
    needmax(z)=max(nd(sel)-ag(sel));                   % intercept needed at slope 1
    % SEC implied by the previous stage's affine bound
    bnd=1+dr*(alpha*b+Bz)./c1b;
    secbmin=min(secbmin,min((log(R2/R1)/gamma+log(1+dr*ag(sel)./C1(sel,z))...
      -max(log(bnd(sel,:)),[],2))/dr));
  end
  if ecm>0, failEC(end+1)=k; end
  if secm<0, failSEC(end+1)=k; end
  alpha=1; Bz=max(needmax,0);                          % keep slope 1, update intercepts
  gaptrue=max(max((C2(sel,:)-C1(sel,:))/dr-ag(sel)));  % true intercept at slope 1
  if ismember(k,[1 2 5 10 20 30 40 50 J-1])
    rows(end+1,:)=[k A t1 ecm secm max(Bz) gaptrue secbmin];
  end
end
fprintf('\n k | region a<= |T1 viol| EC marg/dr | SEC marg/dr | B_rec | B_true | SEC-from-bound\n');
for i=1:size(rows,1)
  fprintf('%3d | %9.2f | %5d | %+10.2f | %+11.2f | %6.3f | %6.3f | %+8.2f\n',rows(i,:));
end
fprintf('Theorem 1 fails at stages: %s\n',mat2str(failT1));
fprintf('EC fails at stages:        %s\n',mat2str(failEC));
fprintf('SEC fails at stages:       %s\n',mat2str(failSEC));
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
