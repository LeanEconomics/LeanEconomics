% Branch and bound for  max Var_w(M/C)  over  {L <= C <= U, lo <= dC <= hi}.
% On a box [c-,c+]: the harmonic mean M is increasing in each C_i, so M <= M(c+), and
% u_i = M/C_i <= M(c+)/c-_i, giving  V <= sum_i w_i (M(c+)/c-_i)^2 - 1, a valid upper bound.
% Branch on the widest coordinate; prune boxes that cannot meet a slope constraint.
function bandb
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; gam=1;
[Pi,y,nu]=tauchen(rho,sigma,nz);
na=400; ag=[0; exp(linspace(log(1e-3),log(2000),na-1))'];
R1=1.04; q=(R1/1.06)^(1/gam); Th1=(beta*R1)^(1/gam);
kap=zeros(J,1); kap(1)=1;
for k=1:J-1, kap(k+1)=kap(k)*R1/(Th1+kap(k)*R1); end
Ha=zeros(nz,J); Hr=zeros(nz,J);
for k=1:J-1
  Ha(:,k+1)=(Pi*(y+Ha(:,k)))/R1;
  x=y+Hr(:,k); pm=zeros(nz,1);
  for z=1:nz, w=Pi(z,:)'; pm(z)=1/(w'*(1./x)); end
  Hr(:,k+1)=min(pm/R1,(1/kap(k+1)-1)*y);
end
c1f=egm(R1,beta,gam,y,Pi,ag,J); m1=y'+R1*ag;
for k=[J-1 40 20]
  allow=Th1/(q*(1-kap(k+1)*R1))-1; worst=0; wz=0; wb=0; tot=0;
  for z=1:nz
    b1=max(m1(:,z)-c1f{k+1}(:,z),0);
    for i=1:40:na
      b=b1(i); if b<=0, continue; end
      mm=y+R1*b; kp=kap(k+1);
      L=kp*(mm+Hr(:,k+1)); U=min(kp*(mm+Ha(:,k+1)),mm); L=min(L,U-1e-12);
      w=Pi(z,:)'; dy=diff(y); lo=kp*dy; hi=dy;
      ub=bb(L,U,lo,hi,w,nz,allow); tot=tot+1;
      if ub>worst, worst=ub; wz=z; wb=b; end
    end
  end
  fprintf(' stage %2d : allowance %.4f ; certified upper bound over %d (z,b) nodes = %.4f  %s',...
          k,allow,tot,worst,tickf(worst<=allow));
  fprintf('   (worst at z=%d, b=%.3f)\n',wz,wb);
end
end
function s=tickf(b), if b, s='PASS'; else, s='fail'; end, end
function best=bb(L,U,lo,hi,w,nz,allow)
S={[L U]}; best=0; nodes=0;
while ~isempty(S) && nodes<4000
  B=S{end}; S(end)=[]; nodes=nodes+1;
  cm=B(:,1); cp=B(:,2);
  d1=cm(2:end)-cp(1:end-1); d2=cp(2:end)-cm(1:end-1);
  if any(d2<lo-1e-12) || any(d1>hi+1e-12), continue; end          % slope-infeasible
  Mp=1/(w'*(1./cp));
  ub=w'*((Mp./cm).^2)-1;
  if ub<=best+1e-9, continue; end
  Cmid=(cm+cp)/2; d=diff(Cmid);
  if all(d>=lo-1e-9) && all(d<=hi+1e-9)
    Mm=1/(w'*(1./Cmid)); v=w'*((Mm./Cmid).^2)-1; best=max(best,v);
  end
  [wd,j]=max(cp-cm);
  if wd<1e-6, best=max(best,ub); continue; end
  mid=(cm(j)+cp(j))/2;
  B1=B; B1(j,2)=mid; B2=B; B2(j,1)=mid;
  S{end+1}=B1; S{end+1}=B2;
end
if nodes>=4000, best=max(best,ubroot(L,U,w)); end
end
function ub=ubroot(L,U,w), Mp=1/(w'*(1./U)); ub=w'*((Mp./L).^2)-1; end
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
