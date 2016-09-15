Rails.application.routes.draw do
  get 'admin/login'
  get 'admin/logout'
  get 'admin/mainpage'
  get 'admin/new_survey'

  post 'admin/login' => 'admin#login'
  post 'admin/new_survey' => 'admin#new_survey'
  
  delete 'admin/logout' => 'admin#logout'
  get 'admin/logout' => 'admin#logout'
    


  get 'user/signup'
  get 'user/login'
  get 'user/mainpage'

  post 'user/signup' => 'user#signup'
  post 'user/login' => 'user#login'
  delete 'user/logout' => 'user#logout'
  delete 'user/delete_user' => 'user#delete_user'

  get 'user/logout' => 'user#logout'
    

end
