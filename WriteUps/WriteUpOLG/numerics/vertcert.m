% Certificate attempt.  In v = 1/C coordinates the objective is h(v) = sum w v^2 / (sum w v)^2, and
% holding all but one coordinate fixed,  dh/dv_j  has the sign of  (v_j B - A)  with
% A = sum_{i/=j} w_i v_i^2, B = sum_{i/=j} w_i v_i.  So h is unimodal with a MINIMUM in each
% coordinate: its maximum over any interval is at an ENDPOINT.  Hence the maximum over the polytope
% is at a point where every coordinate sits at an endpoint of its conditional feasible range, and a
% forward sweep over the chain enumerates those: 2^nz candidates.
function vertcert
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
P=dec2bin(0:2^nz-1)-'0'; rng(11,'twister');
fprintf(' stage | allowance | enumerated max | random check | verdict | margin\n');
for k=[J-1 40 20]
  allow=Th1/(q*(1-kap(k+1)*R1))-1; E=0; Rnd=0;
  for z=1:nz
    b1=max(m1(:,z)-c1f{k+1}(:,z),0);
    for i=1:20:na
      b=b1(i); if b<=0, continue; end
      mm=y+R1*b; kp=kap(k+1);
      L=kp*(mm+Hr(:,k+1)); U=min(kp*(mm+Ha(:,k+1)),mm); L=min(L,U-1e-12);
      w=Pi(z,:)'; dy=diff(y); lo=kp*dy; hi=dy;
      for p=1:size(P,1)
        C=zeros(nz,1); ok=true;
        for j=1:nz
          if j==1, a=L(1); bb=U(1);
          else, a=max(L(j),C(j-1)+lo(j-1)); bb=min(U(j),C(j-1)+hi(j-1)); end
          if a>bb+1e-12, ok=false; break; end
          if P(p,j)==0, C(j)=a; else, C(j)=bb; end
        end
        if ok, E=max(E,vr(C,w)); end
      end
      for t=1:150                        % independent random feasibility check
        C=zeros(nz,1); ok=true;
        for j=1:nz
          if j==1, a=L(1); bb=U(1);
          else, a=max(L(j),C(j-1)+lo(j-1)); bb=min(U(j),C(j-1)+hi(j-1)); end
          if a>bb+1e-12, ok=false; break; end
          C(j)=a+rand*(bb-a);
        end
        if ok, Rnd=max(Rnd,vr(C,w)); end
      end
    end
  end
  if E<=allow, vd='PASS'; else, vd='fail'; end
  fprintf(' %5d | %9.4f | %14.4f | %12.4f | %s | %5.2fx\n',k,allow,E,Rnd,vd,allow/E);
end
fprintf('\n random check must not exceed the enumerated max if the enumeration is complete.\n');
end
function v=vr(C,w), M=1/(w'*(1./C)); v=w'*((M./C).^2)-1; end
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
