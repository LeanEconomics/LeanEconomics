% The crude reachable bound reach(j+1) = R*reach(j) + ymax, started at 0, against the cap the
% refactored theorems need and against the demand curve at the low endpoint.
function reachcheck
ymax=2.98; J=60; alpha=9/25; delta=2/25;
fprintf('   r     |  reach(J+1)  | demand  | reach < demand?\n');
for r=[-0.07 -0.06 -0.04 0 0.0417 0.06 0.08 0.10 0.15]
  R=1+r; x=0; for j=1:J+1, x=R*x+ymax; end
  d=alpha/((1-alpha)*(r+delta));
  fprintf(' %+.4f | %12.2f | %7.2f | %s\n',r,x,d,string(x<d));
end
fprintf('\n at r=-0.07 the bound converges to ymax/(1-R) = %.2f\n',ymax/0.07);
end
