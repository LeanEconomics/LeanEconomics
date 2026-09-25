% Maximise Var_w(M/C) over the POLYTOPE  {L <= C <= U,  kap dy <= dC <= dy}  properly:
% random feasible starts + coordinate ascent on the increments and on C(1).
function polymax
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
rng(7,'twister');
fprintf(' stage | allowance | Var true | polytope max (search) | verdict | margin\n');
for k=[J-1 40 20]
  allow=Th1/(q*(1-kap(k+1)*R1))-1; Vt=0; W=0;
  for z=1:nz
    b1=max(m1(:,z)-c1f{k+1}(:,z),0);
    for i=1:24:na
      b=b1(i); if b<=0, continue; end
      mm=y+R1*b; kp=kap(k+1);
      L=kp*(mm+Hr(:,k+1)); U=min(kp*(mm+Ha(:,k+1)),mm); L=min(L,U);
      Cn=zeros(nz,1);
      for zp=1:nz, Cn(zp)=interp1(ag,c1f{k}(:,zp),b,'linear','extrap'); end
      w=Pi(z,:)'; M=1/(w'*(1./Cn)); Vt=max(Vt,w'*((M./Cn).^2)-1);
      dy=diff(y); lo=kp*dy; hi=dy;
      best=-1;
      for tr=1:60
        C=feas(L,U,lo,hi,nz,tr);
        if isempty(C), continue; end
        v=vr(C,w); 
        for it=1:40                       % coordinate ascent
          imp=false;
          for j=1:nz
            for st=[0.5 0.15 0.04]
              for sg=[1 -1]
                C2=C; C2(j)=C(j)+sg*st*max(1e-6,U(j)-L(j));
                if ok(C2,L,U,lo,hi), v2=vr(C2,w);
                  if v2>v+1e-12, C=C2; v=v2; imp=true; end
                end
              end
            end
          end
          if ~imp, break; end
        end
        best=max(best,v);
      end
      W=max(W,best);
    end
  end
  if W<=allow, vd='PASS'; else, vd='fail'; end
  fprintf(' %5d | %9.4f | %8.4f | %21.4f | %s | %5.2fx\n',k,allow,Vt,W,vd,allow/W);
end
end
function v=vr(C,w), M=1/(w'*(1./C)); v=w'*((M./C).^2)-1; end
function t=ok(C,L,U,lo,hi)
d=diff(C);
t=all(C>=L-1e-10)&&all(C<=U+1e-10)&&all(d>=lo-1e-10)&&all(d<=hi+1e-10);
end
function C=feas(L,U,lo,hi,nz,tr)
for a=1:40
  c1=L(1)+rand*(U(1)-L(1)); d=lo+rand(nz-1,1).*(hi-lo);
  C=[c1;c1+cumsum(d)];
  if ok(C,L,U,lo,hi), return; end
end
C=[];
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
